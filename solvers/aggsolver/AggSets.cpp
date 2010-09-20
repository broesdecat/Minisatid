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

void AggrSet::backtrack(int index) {
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(wlits[index].getLit()));

	wlits[index].setValue(l_Undef);
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for(vector<void*>::size_type i=0; i<nbAgg(); i++){
		getAgg(i)->backtrack(s);
	}
}

AggrSet::AggrSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s):
		currentbestcertain(0),currentbestpossible(0),emptysetvalue(0), aggsolver(s){
	for (int i = 0; i < lits.size(); i++) {
		wlits.push_back(WLV(lits[i], weights[i], l_Undef));
	}
	sort(wlits.begin(), wlits.end());
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
	for(vector<void*>::size_type i=0; i<nbAgg() && confl == nullPtrClause; i++){
		pAgg pa = getAgg(i);

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

bool AggrSet::initialize(){
	doSetReduction();

	setCP(getBestPossible());
	setCC(getEmptySetValue());

	for(vector<void*>::size_type i=0; i<nbAgg();){
		lbool result = getAgg(i)->initialize();
		if(result==l_True){
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			getSolver()->removeHeadWatch(var(getAgg(i)->getHead()));
			//TODO TODO i = eraseAgg(i);
		}else if(result==l_False){
			//UNSAT because always false
			return false;
		}else{
			i++;
		}
	}
	return true;
}

bool AggrSumSet::initialize(){
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
		for(lsagg::const_iterator i=getAggBegin(); i<getAggEnd(); i++){
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

	return AggrSet::initialize();
}


bool AggrProdSet::initialize(){
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

	return AggrSet::initialize();
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
			setCP(getEmptySetValue());
		}
	}
}

Weight	AggrMaxSet::getCombinedWeight(const Weight& first, const Weight& second) const{
	return first>second?first:second;
}

WLit AggrMaxSet::handleOccurenceOfBothSigns(const WLit& one, const WLit& two){
	if(one.getWeight()>two.getWeight()){
		if(getEmptySetValue()<two.getWeight()){
			setEmptySetValue(two.getWeight());
		}
		return one;
	}else{
		if(getEmptySetValue()<one.getWeight()){
			setEmptySetValue(one.getWeight());
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
		setEmptySetValue(getEmptySetValue() + one.getWeight());
		return WLit(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	}else{
		setEmptySetValue(getEmptySetValue() + two.getWeight());
		return WLit(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}


Weight AggrSPSet::getBestPossible() const{
	Weight max = getEmptySetValue();
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
	for (lwlv::const_iterator i=set->getWLBegin(); i<set->getWLEnd(); ++i) {
		reportf(" "); gprintLit((*i).getLit(), (*i).getValue()); reportf("(%s)",printWeight((*i).getWeight()).c_str());
	}
	if(endl){
		reportf(" }\n");
	}else{
		reportf(" }");
	}
}
