//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
Copyright (c) 2006-2009, Maarten Mariën

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <algorithm>

#include "solvers/aggsolver/Agg.hpp"
#include "solvers/aggsolver/AggSets.hpp"
#include "solvers/aggsolver/AggSolver.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

using namespace Aggrs;

AggSet::AggSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
			aggsolver(s){
	for (int i = 0; i < lits.size(); i++) {
		wlits.push_back(WLV(lits[i], weights[i], l_Undef));
	}
	sort(wlits.begin(), wlits.end());
}

void AggrSet::backtrack(int index) {
	if (getStack().size()==0 || var(getStack().back().getLit())!=var(getWL()[index].getLit())) {
		return;	//Only backtrack if it was effectively propagated
	}
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(wlits[index].getLit()));

	wlits[index].setValue(l_Undef);
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for(lsagg::const_iterator i=getAgg().begin(); i<getAgg().end(); i++){
		(*i)->backtrack(s);
	}
}

AggrSet::AggrSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
		AggSet(lits, weights, s), currentbestcertain(0),currentbestpossible(0),emptysetvalue(0){
}

AggrMaxSet::AggrMaxSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
		AggrSet(lits, weights, s){
	name = "MAX";
	//FIXME moet eigenlijk een voorstelling van -infinity zijn
	//ik had eerst: |minimum van de set| -1, maar de bound zelf kan NOG lager liggen, dus dan is het fout
	emptysetvalue = Weight(INT_MIN);
	assert(emptysetvalue<=INT_MIN);
}

AggrSPSet::AggrSPSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
		AggrSet(lits, weights, s){}

AggrSumSet::AggrSumSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
		AggrSPSet(lits, weights, s){
	name = "SUM";
	emptysetvalue = 0;
}

AggrProdSet::AggrProdSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
		AggrSPSet(lits, weights, s){
	name = "PROD";
	emptysetvalue = 1;
}

rClause AggrSet::propagate(const Lit& p, const AggrWatch& ws){
	Occurrence tp;
    if (ws.getType()==POS){
    	tp = sign(p)? NEG : POS;
    }else{
    	tp = sign(p)? POS : NEG;
    }

	stack.push_back(PropagationInfo(p, wlits[ws.getIndex()].getWeight(),tp, getCC(), getCP()));
	wlits[ws.getIndex()].setValue(tp==POS?l_True:l_False);
	tp==POS? addToCertainSet(wlits[ws.getIndex()]):removeFromPossibleSet(wlits[ws.getIndex()]);

	rClause confl = nullPtrClause;
	for(lsagg::const_iterator i=getAgg().begin(); i<getAgg().end() && confl == nullPtrClause; i++){
		pAgg pa = (*i);

		//TODO dit is vrij lelijk
		if(getSolver()->getPCSolver()->modes().verbosity>=4){
			reportf("Propagating into aggr: ");
			Aggrs::printAggrExpr(pa);
		}

		lbool hv = pa->getHeadValue();
		if(hv != l_Undef){ //head is already known
			assert(pa->canPropagateHead(getCC(), getCP())!=(hv==l_True?l_False:l_True));	//A conflicting propagation is not possible if we have complete propagation
			confl = pa->propagate(hv==l_True);
		}else{ //head is not yet known, so at most the head can be propagated
			lbool result = pa->canPropagateHead(getCC(), getCP());
			if(result!=l_Undef){
				rClause cc = getSolver()->notifySATsolverOfPropagation(result==l_True?pa->getHead():~pa->getHead(), new AggrReason(*i, p, CPANDCC, true));
				confl = cc;
			}
		}
	}
	return confl;
}

/*
 * To be able to handle multiple times the same literal and also its negation, we will be checking here if the set conforms to that
 * If it does not, a duplicate will be created, which will only be used in this aggregate and which conforms to the rules
 */
bool compareLits(const WLit& one, const WLit& two) {
	return var(one.getLit())<var(two.getLit());
}

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
void AggrSet::doSetReduction() {
	lwlv& oldset = wlits;
	lwlv newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(lwlv::size_type i=1; i<oldset.size(); i++){
		WLV oldl = newset[indexinnew];
		WLV newl = oldset[i];
		if(var(oldl.getLit())==var(newl.getLit())){ //same variable
			setisreduced = true;
			if(oldl.getLit()==newl.getLit()){ //same literal, keep combined weight
				Weight w = getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WLV(oldl.getLit(), w, oldl.getValue());
			}else{ //opposite signs
				WLit wl = handleOccurenceOfBothSigns(oldl, newl);
				newset[indexinnew] = WLV(wl.getLit(), wl.getWeight(), oldl.getValue());
			}
		}else{
			newset.push_back(newl);
			indexinnew++;
		}
	}

	lwlv newset2;
	for(lwlv::size_type i=0; i<newset.size(); i++){
		if(!isNeutralElement(newset[i].getWeight())){
			newset2.push_back(newset[i]);
		}else{
			setisreduced = true;
		}
	}

	if(setisreduced){
		wlits.clear();
		wlits.insert(wlits.begin(), newset2.begin(), newset2.end());
	}

	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(wlits.begin(), wlits.end());
}

pSet AggrSet::initialize(bool& unsat){
	unsat = false;
	if(aggregates.size()==0){
		return NULL;
	}
	doSetReduction();

	setCP(getBestPossible());
	setCC(getESV());

	for(vector<void*>::size_type i=0; i<nbAgg();){
		lbool result = getAgg(i)->initialize();
		if(result==l_True){
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			getSolver()->removeHeadWatch(var(getAgg(i)->getHead()));
			//TODO TODO i = eraseAgg(i);
		}else if(result==l_False){
			//UNSAT because always false
			unsat = true;
		}else{
			i++;
		}
	}
	return this;
}

pSet AggrSumSet::initialize(bool& unsat){
	unsat = false;
	if(aggregates.size()==0){
		return NULL;
	}

	//Calculate the total negative weight to make all weight positive
	lwlv wlits2;
	Weight totalneg(0);
	for(lwlv::const_iterator i=wlits.begin(); i<wlits.end(); i++){
		if ((*i).getWeight() < 0) {
			totalneg-=(*i).getWeight();
		}
	}
	if(totalneg > 0){
		for(lwlv::const_iterator i=wlits.begin(); i<wlits.end(); i++){
			wlits2.push_back(WLV((*i).getLit(), abs((*i).getWeight()), (*i).getValue()));
		}
		wlits = wlits2;
		for(lsagg::const_iterator i=getAgg().begin(); i<getAgg().end(); i++){
			(dynamic_cast<SumAgg*>(*i))->addToBounds(totalneg);
		}
	}

#ifdef INTWEIGHT
	//Test whether the total sum of the weights is not infinity for intweights
	Weight total(0);
	for(lwlv::const_iterator i=wlits.begin(); i<wlits.end(); i++){
		if(INT_MAX-total < (*i).getWeight()){
			throw idpexception("The total sum of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total += (*i).getWeight();
	}
#endif

	return AggrSet::initialize(unsat);
}


pSet AggrProdSet::initialize(bool& unsat){
	unsat = false;
	if(aggregates.size()==0){
		return NULL;
	}
#ifdef INTWEIGHT
	//Test whether the total product of the weights is not infinity for intweights
	Weight total(1);
	for(lwlv::const_iterator i=wlits.begin(); i<wlits.end(); i++){
		if(INT_MAX/total < (*i).getWeight()){
			throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total *= (*i).getWeight();
	}
#endif

	return AggrSet::initialize(unsat);
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
void AggrSet::getExplanation(pAgg agg, vec<Lit>& lits, AggrReason& ar) const{
	assert(ar.getAgg() == agg);
	assert(agg->getSet()==this);

	const Lit& head = agg->getHead();

	if(!ar.isHeadReason() && ar.getIndex() >= agg->getHeadIndex()){
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(getSolver()->isTrue(head)?~head:head);
	}

	const AggrSet* s = this;

	//assert(ar.isHeadReason() || getPCSolver()->getLevel(ar.getLit())<=s->getStackSize());

//	This is correct, but not minimal enough. We expect to be able to do better
//	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
//		lits.push(~(*i).getLit());
//	}

	int counter = 0;
	if(ar.getExpl()!=HEADONLY){
		for(lprop::const_iterator i=s->getStack().begin(); counter<ar.getIndex() && i<s->getStack().end(); i++,counter++){
		//for(lprop::const_iterator i=s->getStackBegin(); var(ar.getLit())!=var((*i).getLit()) && i<s->getStackEnd(); i++){
			switch(ar.getExpl()){
			case BASEDONCC:
				if((*i).getType()==POS){
					lits.push(~(*i).getLit());
				}
				break;
			case BASEDONCP:
				if((*i).getType()==NEG){
					lits.push(~(*i).getLit());
				}
				break;
			case CPANDCC:
				lits.push(~(*i).getLit());
				break;
			default:
				assert(false);
				break;
			}
		}
	}

	//TODO de nesting van calls is vrij lelijk en onefficient :)
	if(s->getSolver()->verbosity()>=5){

		reportf("STACK: ");
		for(lprop::const_iterator i=s->getStack().begin(); i<s->getStack().end(); i++){
			gprintLit((*i).getLit()); reportf(" ");
		}
		reportf("\n");


		reportf("Aggregate explanation for ");
		if(ar.isHeadReason()){
			gprintLit(head);
		}else{
			reportf("(index %d)", ar.getIndex());
			gprintLit((*(s->getWL().begin()+ar.getIndex())).getLit());
		}

		reportf(" is");
		for(int i=0; i<lits.size(); i++){
			reportf(" ");
			gprintLit(lits[i]);
		}
		reportf("\n");
	}
}

/*****************
 * MAX AGGREGATE *
 *****************/

Weight AggrMaxSet::getBestPossible() const{
	return wlits.back().getWeight();
}

void AggrMaxSet::addToCertainSet(const WLit& l){
	if(l.getWeight()>getCC()){
		setCC(l.getWeight());
	}
}

void AggrMaxSet::removeFromPossibleSet(const WLit& l){
	if(l.getWeight()==getCP()){
		bool found = false;
		for(lwlv::reverse_iterator i=wlits.rbegin(); !found && i<wlits.rend(); i++){
			if((*i).getValue() != l_False){
				setCP((*i).getWeight());
				found = true;
			}
		}
		if(!found){
			setCP(getESV());
		}
	}
}

Weight	AggrMaxSet::getCombinedWeight(const Weight& first, const Weight& second) const{
	return first>second?first:second;
}

WLit AggrMaxSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	if(one.getWeight()>two.getWeight()){
		if(getESV()<two.getWeight()){
			setESV(two.getWeight());
		}
		return one;
	}else{
		if(getESV()<one.getWeight()){
			setESV(one.getWeight());
		}
		return two;
	}
}


/*****************
 * SUM AGGREGATE *
 *****************/

Weight	AggrSumSet::add(const Weight& lhs, const Weight& rhs) const{
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && INT_MAX-lhs < rhs){
		return INT_MAX;
	}else if(lhs<0 && rhs<0 && INT_MIN-lhs>rhs){
		return INT_MIN;
	}
#endif
	return lhs+rhs;
}
Weight	AggrSumSet::remove(const Weight& lhs, const Weight& rhs) const{
	return lhs-rhs;
}
Weight	AggrProdSet::add(const Weight& lhs, const Weight& rhs) const{
#ifdef INTWEIGHT
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0){
		l= -l;
		sign = true;
	}
	if(r<0){
		r = -r;
		sign = !sign;
	}
	if(INT_MAX/l < r){
		return sign?INT_MIN:INT_MAX;
	}
#endif
	return lhs*rhs;
}
Weight	AggrProdSet::remove(const Weight& lhs, const Weight& rhs) const{
	if(rhs==0){
		return 0;
	}else{
		return lhs/rhs;
	}
}

WLit AggrSumSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	if(one.getWeight()<two.getWeight()){
		setESV(getESV() + one.getWeight());
		return WLit(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	}else{
		setESV(getESV() + two.getWeight());
		return WLit(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}


Weight AggrSPSet::getBestPossible() const{
	Weight max = getESV();
	for (lwlv::const_iterator j = wlits.begin(); j < wlits.end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

void AggrSPSet::addToCertainSet(const WLit& l){
	setCC(this->add(getCC(), l.getWeight()));
}

void AggrSPSet::removeFromPossibleSet(const WLit& l){
	setCP(this->remove(getCP(), l.getWeight()));
}

/**
 * multi-set semantics!
 */
Weight	AggrSPSet::getCombinedWeight(const Weight& first, const Weight& second) const{
	return this->add(first, second);
}

WLit AggrProdSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	reportf("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ");
	gprintLit(one.getLit()); reportf("or "); gprintLit(two.getLit()); reportf("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}


pSet AggrCardSet::initialize(bool& unsat){
	unsat = false;
	if(getAgg().size()==0){
		return NULL;
	}

	//decide whether to use watched sets
	ws = true;

	//decide on number
	bool lb=false, ub=false, headsknown = true;
	if(getAgg().size()>1){
		throw new idpexception("No implementation for this yet");
	}
	pAgg agg = getAgg()[0];
	if(agg->isLower()){
		lb = true;
	}
	if(agg->isUpper()){
		ub = true;
	}
	if((ub && lb) || (!ub && !lb)){
		throw new idpexception("No implementation for this yet");
	}
	if(getSolver()->value(agg->getHead())==l_Undef){
		headsknown = false;
	}

	if(headsknown && lb){
		numberam = 0;
		numberm = agg->getLowerBound()+1;
	}else if(headsknown && ub){
		numberam = 0;
		numberm = getWL().size()-agg->getUpperBound()+1;
	}else{
		if(lb){
			numberam = getWL().size()-agg->getLowerBound();
			numberm = agg->getLowerBound();
		}else if(ub){
			numberam = agg->getUpperBound();
			numberm = getWL().size()-agg->getUpperBound();
		}
	}

	//initialize watch set
	int montaken = 0, amontaken = 0;
	for(lwlv::const_iterator i=getWL().begin(); i<getWL().end(); i++){
		bool monfound = false, amonfound = false;
		const Lit& l = (*i).getLit();
		if(montaken<numberm){
			if(agg->isMonotone(*i) && getSolver()->value(l)!=l_False){
				watched.push_back(l);
				montaken++;
				monfound = true;
			}else if(!agg->isMonotone(*i) && getSolver()->value(l)!=l_True){
				watched.push_back(~l);
				montaken++;
				monfound = true;
			}
		}else if(!monfound && amontaken<numberam){
			if(!agg->isMonotone(*i) && getSolver()->value(l)!=l_False){
				watched.push_back(l);
				amontaken++;
				amonfound = false;
			}else if(agg->isMonotone(*i) && getSolver()->value(l)!=l_True){
				watched.push_back(~l);
				amontaken++;
				amonfound = false;
			}
		}else if(!monfound && !amonfound){
			nonwatched.push_back(l);
		}
	}
	if(headsknown && montaken<numberm){
		if(montaken<numberm-1){
			unsat = true;
			return this;	//Not enough monotone, non-false literals to satisfy the aggregate
		}else{
			//can propagate all in the watched set
			for(int i=0; i<watched.size(); i++){
				rClause confl = getSolver()->notifySATsolverOfPropagation(watched[i], new AggrReason(agg, watched[i], BASEDONCC, false));
				if(confl!=nullPtrClause){
					unsat = true;
					return this;
				}
			}
		}
	}else if(!headsknown){
		if(montaken<numberm){
			//head is false, propagate it
			rClause confl = getSolver()->notifySATsolverOfPropagation(~agg->getHead(), new AggrReason(agg, ~agg->getHead(), BASEDONCC, true));
			if(confl!=nullPtrClause){
				unsat = true;
				return this;
			}
		}else if(amontaken<numberam){
			//head is true, propagate it
			rClause confl = getSolver()->notifySATsolverOfPropagation(agg->getHead(), new AggrReason(agg, agg->getHead(), BASEDONCC, true));
			if(confl!=nullPtrClause){
				unsat = true;
				return this;
			}
		}
	}
	for(int i=0; i<watched.size(); i++){
		getSolver()->addTempWatch(watched[i], this);
	}
	return this;
}
rClause AggrCardSet::propagate(const Lit& l, bool& removewatch){
	//find the index
	int index = 0;
	for(int index=0; index<watched.size(); index++){
		if(~l==watched[index]){
			break;
		}
	}
	//find a new one if possible
	pAgg agg = getAgg()[0];
	bool findmon = agg->isMonotone(WLV(l, 1, l_True));
	int swapindex = -1;
	for(int i=0; swapindex==-1 && i<nonwatched.size(); i++){
		if(findmon){
			if(agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_False){
				swapindex=i;
			}else if(!agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_True){
				swapindex=i;
			}
		}else{
			if(!agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_False){
				swapindex=i;
			}else if(agg->isMonotone(WLV(nonwatched[i], 1, l_Undef)) && getSolver()->value(nonwatched[i])!=l_True){
				swapindex=i;
			}
		}
	}
	if(swapindex==-1){
		//no other found, do propagation
		//TODO
	}else{
		Lit temp = watched[index];
		watched[index] = nonwatched[swapindex];
		nonwatched[swapindex] = temp;
	}

	return nullPtrClause;
}


/************************
 * RECURSIVE AGGREGATES *
 ************************/

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */

bool AggrSet::oppositeIsJustified(const WLV& elem, vec<int>& currentjust, bool real) const{
	if(real){
		return elem.getValue()!=l_True;
	}else{
		return elem.getValue()!=l_True && (!sign(elem.getLit()) || isJustified(var(elem.getLit()), currentjust));
	}
}

bool AggrSet::isJustified(const WLV& elem, vec<int>& currentjust, bool real) const{
	if(real){
		return elem.getValue()!=l_False;
	}else{
		return elem.getValue()!=l_False && (sign(elem.getLit()) || isJustified(var(elem.getLit()), currentjust));
	}
}

bool AggrSet::isJustified(Var x, vec<int>& currentjust) const{
	return currentjust[x]==0;
}

///////
// DEBUG
///////

void Aggrs::printAggrSet(pSet set, bool endl){
	reportf("%s{", set->getName().c_str());
	for (lwlv::const_iterator i=set->getWL().begin(); i<set->getWL().end(); ++i) {
		reportf(" "); gprintLit((*i).getLit(), (*i).getValue()); reportf("(%s)",printWeight((*i).getWeight()).c_str());
	}
	if(endl){
		reportf(" }\n");
	}else{
		reportf(" }");
	}
}
