#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/AggSolver.hpp"

using namespace Aggrs;

AggSet::AggSet(const vector<Lit>& lits, const vector<Weight>& weights){
	for(int i=0; i<lits.size(); i++){
		wlits.push_back(WL(lits[i], weights[i]));
	}
	sort(wlits.begin(), wlits.end());
}

AggComb::AggComb(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
		aggsolver(solver), set(new AggSet(lits, weights)){
}

void FWAgg::backtrack(int index) {
	/*if (getStack().size()==0 || var(getStack().back().getLit())!=var(getWL()[index].getLit())) {
		return;	//Only backtrack if it was effectively propagated
	}
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(getWL()[index].getLit()));

	//getSet()->getWL()[index].setValue(l_Undef);
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for(vpagg::const_iterator i=getAgg().begin(); i<getAgg().end(); i++){
		//TODO bactrack aggregates
	}*/
}

FWAgg::FWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights):
		AggComb(solver, lits, weights), currentbestcertain(0),currentbestpossible(0),emptysetvalue(0){
}

rClause FWAgg::propagate(Watch* ws){
	/*Occurrence tp;
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
				rClause cc = getSolver()->notifySATsolverOfPropagation(result==l_True?pa->getHead():~pa->getHead(), new AggReason(*i, p, CPANDCC, true));
				confl = cc;
			}
		}
	}
	return confl;*/
}

/*
 * Allow sorting of WL, getting same literals next to each other
 */
bool compareLits(const WL& one, const WL& two) {
	return var(one.getLit())<var(two.getLit());
}

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
void FWAgg::doSetReduction() {
	vwl oldset = getSet()->getWL();
	vwl newset;

	//Sort all wlits according to the integer representation of their literal (to get all literals next to each other)
	std::sort(oldset.begin(), oldset.end(), compareLits);

	int indexinnew = 0;
	newset.push_back(oldset[indexinnew]);

	bool setisreduced = false;
	for(vwl::size_type i=1; i<oldset.size(); i++){
		WL oldl = newset[indexinnew];
		WL newl = oldset[i];
		if(var(oldl.getLit())==var(newl.getLit())){ //same variable
			setisreduced = true;
			if(oldl.getLit()==newl.getLit()){ //same literal, keep combined weight
				Weight w = getCombinedWeight(newl.getWeight(), oldl.getWeight());
				newset[indexinnew] = WL(oldl.getLit(), w);
			}else{ //opposite signs
				WL wl = handleOccurenceOfBothSigns(oldl, newl);
				newset[indexinnew] = WL(wl.getLit(), wl.getWeight());
			}
		}else{
			newset.push_back(newl);
			indexinnew++;
		}
	}

	vwl newset2;
	for(vwl::size_type i=0; i<newset.size(); i++){
		if(!isNeutralElement(newset[i].getWeight())){
			newset2.push_back(newset[i]);
		}else{
			setisreduced = true;
		}
	}

	if(setisreduced){
		getSet()->setWL(newset2);
	}
}

pcomb FWAgg::initialize(bool& unsat){
	unsat = false;
	if(getAgg().size()==0){
		return NULL;
	}
	doSetReduction();

	setCP(getBestPossible());
	setCC(getESV());

	int i=0, j=0;
	for(; !unsat && i<aggregates.size(); i++){
		lbool result = initialize(aggregates[i]);
		if(result==l_True){
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			getSolver()->removeHeadWatch(var(aggregates[i]->getHead()));
			delete aggregates[i];
		}else if(result==l_False){
			//UNSAT because always false
			unsat = true;
		}else{
			aggregates[j++] = aggregates[i];
		}
	}
	aggregates.resize(j);

	return this;
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
void FWAgg::getExplanation(pagg agg, vec<Lit>& lits, AggReason& ar) const{
	//assert(ar.getAgg() == agg);
	//assert(agg->getSet()==this);

	const Lit& head = agg->getHead();

	/*TODO if(!ar.isHeadReason() && ar.getIndex() >= agg->getHeadIndex()){
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(getSolver()->isTrue(head)?~head:head);
	}*/

	//assert(ar.isHeadReason() || getPCSolver()->getLevel(ar.getLit())<=s->getStackSize());

//	This is correct, but not minimal enough. We expect to be able to do better
//	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
//		lits.push(~(*i).getLit());
//	}

	int counter = 0;
	if(ar.getExpl()!=HEADONLY){
		for(vprop::const_iterator i=getStack().begin(); counter<ar.getIndex() && i<getStack().end(); i++,counter++){
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
	if(getSolver()->verbosity()>=5){

		reportf("STACK: ");
		for(vprop::const_iterator i=getStack().begin(); i<getStack().end(); i++){
			gprintLit((*i).getLit()); reportf(" ");
		}
		reportf("\n");


		reportf("Aggregate explanation for ");
		if(ar.isHeadReason()){
			gprintLit(head);
		}else{
			reportf("(index %d)", ar.getIndex());
			gprintLit((*(getWL().begin()+ar.getIndex())).getLit());
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

Weight MaxFWAgg::getBestPossible() const{
	return getWL().back().getWeight();
}

void MaxFWAgg::addToCertainSet(const WL& l){
	if(l.getWeight()>getCC()){
		setCC(l.getWeight());
	}
}

void MaxFWAgg::removeFromPossibleSet(const WL& l){
	if(l.getWeight()==getCP()){
		bool found = false;
		for(int i=0; i<getWL().size(); i++){
			if(truth[i] != l_False){
				setCP(getWL()[i].getWeight());
				found = true;
			}
		}
		if(!found){
			setCP(getESV());
		}
	}
}

Weight MaxFWAgg::getCombinedWeight(const Weight& first, const Weight& second) const{
	return first>second?first:second;
}

WL MaxFWAgg::handleOccurenceOfBothSigns(const WL& one, const WL& two){
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

/************************
 * RECURSIVE AGGREGATES *
 ************************/

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool FWAgg::oppositeIsJustified(const WL& l, vec<int>& currentjust, bool real) const{
	if(real){
		return getSolver()->value(l.getLit())!=l_True;
	}else{
		return getSolver()->value(l.getLit())!=l_True && (!sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool FWAgg::isJustified(const WL& l, vec<int>& currentjust, bool real) const{
	if(real){
		return getSolver()->value(l.getLit())!=l_False;
	}else{
		return getSolver()->value(l.getLit())!=l_False && (sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool FWAgg::isJustified(Var x, vec<int>& currentjust) const{
	return currentjust[x]==0;
}

///////
// DEBUG
///////

void Aggrs::printAgg(AggComb const * const c){
	/*reportf("%s{", set->getName().c_str());
	for (lwlv::const_iterator i=set->getWL().begin(); i<set->getWL().end(); ++i) {
		reportf(" "); gprintLit((*i).getLit(), (*i).getValue()); reportf("(%s)",printWeight((*i).getWeight()).c_str());
	}
	if(endl){
		reportf(" }\n");
	}else{
		reportf(" }");
	}*/
}
