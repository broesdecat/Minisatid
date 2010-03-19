#include "AggSets.h"
#include <algorithm>
#include "Agg.h"
#include "AggSolver.h"

using namespace Aggrs;

void AggrSet::backtrack(int index) {
	//BELANGRIJK: hier had ik een referentie gezet en dan deed ik pop, wat dus niet mag, want dan is die value kwijt!
	PropagationInfo pi = stack.back();
	stack.pop_back();

	assert(pi.getType()!=HEAD && var(pi.getLit())==var(wlits[index].getLit()));

	wlits[index].setValue(l_Undef);
	setCC(pi.getPC());
	setCP(pi.getPP());
}

AggrSet::AggrSet(vec<Lit>& lits, vector<Weight>& weights, weak_ptr<AggSolver> s):
		currentbestcertain(0),currentbestpossible(0),emptysetvalue(0), aggsolver(s){
	for (int i = 0; i < lits.size(); i++) {
		wlits.push_back(WLV(lits[i], weights[i], l_Undef));
	}
	sort(wlits.begin(), wlits.end());
}

Clause* AggrSet::propagate(const Lit& p, const AggrWatch& ws){
	Occurrence tp;
    if (ws.getType()==POS){
    	tp = sign(p)? NEG : POS;
    }else{
    	tp = sign(p)? POS : NEG;
    }

	stack.push_back(PropagationInfo(p, wlits[ws.getIndex()].getWeight(),tp, getCC(), getCP()));
	wlits[ws.getIndex()].setValue(tp==POS?l_True:l_False);
	tp==POS? addToCertainSet(wlits[ws.getIndex()]):removeFromPossibleSet(wlits[ws.getIndex()]);

	Clause* confl = NULL;
	for(lwagg::const_iterator i=getAggBegin(); i<getAggEnd() && confl==NULL; i++){
		pAgg pa = (*i).lock();
		lbool hv = pa->getHeadValue();
		if(hv != l_Undef){ //head is already known
			assert(pa->canPropagateHead()!=(hv==l_True?l_False:l_True));	//A conflicting propagation is not possible if we have complete propagation
			confl = pa->propagate(hv==l_True);
		}else{ //head is not yet known, so at most the head can be propagated
			lbool result = pa->canPropagateHead();
			if(result!=l_Undef){
				confl = getSolver()->notifySATsolverOfPropagation(result==l_True?pa->getHead():~pa->getHead(), new AggrReason(*i, true));
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

	if(setisreduced){
		wlits.clear();
		wlits.insert(wlits.begin(), newset.begin(), newset.end());
	}

	//important to sort again to guarantee that it is sorted according to the weights
	std::sort(wlits.begin(), wlits.end());
}

void AggrSet::initialize(){
	doSetReduction();
	setCP(getBestPossible());
	setCC(getEmptySetValue());
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
	return lhs+rhs;
}
Weight	AggrSumSet::remove(const Weight& lhs, const Weight& rhs) const{
	return lhs-rhs;
}
Weight	AggrProdSet::add(const Weight& lhs, const Weight& rhs) const{
	return lhs*rhs;
}
Weight	AggrProdSet::remove(const Weight& lhs, const Weight& rhs) const{
	return rhs==0?0:lhs/rhs;
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
	gprintLit(one.getLit());
	reportf("or ");
	gprintLit(two.getLit());
	reportf("by a tseitin.\n");
	exit(3);
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
