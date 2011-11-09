/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/FullyWatched.hpp"

#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "theorysolvers/PCSolver.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace std;
using namespace MinisatID;

typedef Agg* pagg;
typedef Watch* pw;

FWAgg::FWAgg(TypedSet* set) :
	AggPropagator(set) {

}

void FWAgg::initialize(bool& unsat, bool& sat) {
	if (getSet().getAgg().size() == 0) {
		sat = true;	return;
	}

	trail.push_back(new FWTrail(0, getSet().getType().getMinPossible(getSet()), getSet().getType().getMaxPossible(getSet())));

	int counter = 0;
	for (auto i = getSet().getAggNonConst().cbegin(); !unsat && i < getSet().getAggNonConst().cend();) {
		pagg agg = (*i);
		if(not agg->isOptim()){
			lbool result = initialize(*agg);
			if (result == l_True) {
				//If after initialization, the head will have a fixed value, then this is
				//independent of any further propagations within that aggregate.
				//BUT ONLY if it is not defined (or at a later stage, if it cannot be in any loop)
				// FIXME remove headwatch
				//getSet().removeHeadWatch(var(agg->getHead()));
				//i = getSet().getAggNonConst().erase(i);
				//continue;
			} else if (result == l_False) {
				unsat = true; //UNSAT because always false
				return;
			}
		}
		agg->setIndex(counter++);
		++i;
	}

	if(getSet().getAgg().size()==0){
		sat = true; return;
	}

	for (auto j = getSet().getWL().cbegin(); j < getSet().getWL().cend(); ++j) {
		const Lit& l = (*j).getLit();
		Watch *pos, *neg;
		pos = new Watch(getSetp(), l, (*j).getWeight(), true, false);
		neg = new Watch(getSetp(), not l, (*j).getWeight(), false, false);
		getSet().getPCSolver().accept(pos);
		getSet().getPCSolver().accept(neg);
	}

	AggPropagator::initialize(unsat, sat);
}

/**
 * Returns true if this aggregate can be propagated in the initialization, so it will never change truth value
 * and can be left out of any propagations.
 * Returns false if the aggregate is certainly unsat.
 */
lbool FWAgg::initialize(const Agg& agg) {
	rClause confl = nullPtrClause;

	lbool hv = canPropagateHead(agg, getCC(), getCP());
	bool alwaystrue = false;
	if (hv != l_Undef) {
		alwaystrue = true;
		//reportf("No more propagations for %d", getPrintableVar(var(head)));
	}
	if (hv == l_True) {
		confl = getSet().notifySolver(new HeadReason(agg, agg.getHead()));
	} else if (hv == l_False) {
		confl = getSet().notifySolver(new HeadReason(agg, not agg.getHead()));
	}
	if (confl != nullPtrClause) {
		return l_False;
	}

	return alwaystrue ? l_True : l_Undef;
}

void FWAgg::backtrack(int untillevel){
	while(getTrail().back()->level>untillevel){
		//report("Backtrack trail of FW\n");
		delete getTrail().back();
		getTrail().pop_back();
		getTrail().back()->start = getTrail().back()->props.size();
	}
}

/**
 * Returns non-owning pointer
 */
void FWAgg::propagate(int level, Watch* watch, int aggindex) {
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return nullPtrClause;
	//}

	FWTrail* fwobj = getTrail().back();
	if(fwobj->level<level){
		getTrail().push_back(new FWTrail(level, fwobj->CBC, fwobj->CBP));
		fwobj = getTrail().back();
		getSet().getPCSolver().acceptForBacktrack(getSetp());
	}

	if(fwobj->start == fwobj->props.size()){
		getSet().getPCSolver().acceptForPropagation(getSetp());
	}

	fwobj->props.push_back(PropagationInfo(watch->getPropLit(), 0, HEAD));
	fwobj->headindex.push_back(aggindex);
	fwobj->headtime.push_back(fwobj->props.size());
}

void FWAgg::propagate(const Lit& p, Watch* ws, int level) {
	FWTrail* fwobj = getTrail().back();
	if(fwobj->level<level){
		getTrail().push_back(new FWTrail(level, fwobj->CBC, fwobj->CBP));
		fwobj = getTrail().back();
		getSet().getPCSolver().acceptForBacktrack(getSetp());
	}
	if(fwobj->start == fwobj->props.size()){
		getSet().getPCSolver().acceptForPropagation(getSetp());
	}

#ifdef DEBUG
	assert(ws->getSet()==getSetp());
	bool foundlit = false;
	for(vwl::const_iterator i=getSet().getWL().cbegin(); i<getSet().getWL().cend() ; ++i){
		if(var(i->getLit())==var(p)){
			foundlit = true;
		}
	}
	assert(foundlit);

	bool found = false;
	found = true; // FIXME it SHOULD be in the propagation queue now
	assert(found);
#endif

	assert(fwobj->level == level && level == getSet().getPCSolver().getLevel(var(p)));
	fwobj->props.push_back(PropagationInfo(p, ws->getWeight(), ws->getType()));
}

rClause FWAgg::propagateAtEndOfQueue(){
	rClause confl = nullPtrClause;

	FWTrail& fwobj = *getTrail().back();

	// FIXME should never have called propagate then! (were originally asserts
	if(fwobj.start==fwobj.props.size() || fwobj.level!=getSet().getPCSolver().getCurrentDecisionLevel()){
		return confl;
	}

	bool changedcp = false;
	bool changedcc = false;
	for(uint i=fwobj.start; i<fwobj.props.size(); ++i){
		const PropagationInfo& p = fwobj.props[i];
		if(p.getType()!=HEAD){
			WL wl(p.getLit(), p.getWeight());
			if(p.getType()==POS){
				addToCertainSet(wl);
				changedcc = true;
			}else{
				removeFromPossibleSet(wl);
				changedcp = true;
			}
		}
	}
	fwobj.start = fwobj.props.size();

	for(vector<int>::const_iterator i=fwobj.headindex.cbegin(); confl==nullPtrClause && i<fwobj.headindex.cend(); ++i){
		pagg agg = getSet().getAgg()[*i];
		assert(agg->getSet()->getAgg()[agg->getIndex()]==agg && *i == agg->getIndex());
		lbool headval = value(agg->getHead());
		assert(headval!=l_Undef);
		confl = propagateSpecificAtEnd(*agg, headval==l_True);
	}

	if(changedcc || changedcp){
		//TODO find aggregate with most stringent bound and only propagate that one!
		for (agglist::const_iterator i = getSet().getAgg().cbegin(); confl == nullPtrClause && i<getSet().getAgg().cend(); ++i){
			const Agg& pa = **i;

			if (getSet().verbosity() >= 6) {
				clog <<"Propagating into aggr: ";
				MinisatID::print(getSet().verbosity(), pa, false);
				clog <<", CC = " <<getCC() <<", CP = " <<getCP() <<"\n";
			}

			lbool hv = value(pa.getHead());

			//TODO ugly
			if(hv==l_True && pa.getSign()==AGGSIGN_LB && !changedcp){
				continue;
			}
			if(hv==l_True && pa.getSign()==AGGSIGN_UB && !changedcc){
				continue;
			}
			if(hv==l_False && pa.getSign()==AGGSIGN_LB && !changedcc){
				continue;
			}
			if(hv==l_False && pa.getSign()==AGGSIGN_UB && !changedcp){
				continue;
			}

			lbool result = canPropagateHead(pa, getCC(), getCP());
			if(hv!=l_Undef){
				if(result==l_Undef){
					confl = propagateSpecificAtEnd(pa, hv == l_True);
				}else if(hv!=result){
					confl = getSet().notifySolver(new HeadReason(pa, result==l_True?pa.getHead():not pa.getHead()));
				}
			}else if(result!=l_Undef){
				confl = getSet().notifySolver(new HeadReason(pa, result==l_True?pa.getHead():not pa.getHead()));
			}
		}
	}

	return confl;
}

lbool MinisatID::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) {
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return headvalue[agg.getIndex()];
	//}

	lbool result = l_Undef;

	//add if derived: headproptime[agg.getIndex()] = getStack().size();
	const Weight& b = agg.getCertainBound();
	if(agg.hasUB()){
		if(CC > b){
			result = l_False;
		}else if(CP <= b){
			result = l_True;
		}
	}else{
		if(CC>= b){
			result = l_True;
		}else if(CP < b){
			result = l_False;
		}
	}

	return result;
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 *
 * !headreason && headtrue: CASE 1
 * 		add ~head
 * 		if proplit mono: remove from set
 * 			else add to set
 * 		while not falsified, add to values: inset if become true, remove if became false
 * 			add to reason if !inset && mono || inset && am
 *
 * !headreason && headfalse: CASE 2
 * 		add head
 * 		if proplit mono: add to set
 * 			else remove from set
 * 		while not satisfied,
 * 			add to set if become true, remove if became false
 * 			add lit to reason if mono && true || am && false
 *
 * headreason && explain headtrue:
 * 		CASE 1 without adding head
 *
 * headreason && explain headfalse:
 * 		CASE 2 without adding head
 */
void SPFWAgg::checkAddToExplan(bool& stop, Weight& min, Weight& max, const PropagationInfo& propinfo, const Agg& agg, bool caseone, vector<PropagationInfo>& reasons){
	bool inset = propinfo.getType()==POS;
	addValue(getSet().getType(), propinfo.getWeight(), inset, min, max);
	bool monoweight = getSet().getType().isMonotone(agg, propinfo.getWeight());
	bool monolit = monoweight?inset:!inset;
	bool add = false;
	if(caseone && !monolit){
		add = true;
	}else if(!caseone && monolit){
		add = true;
	}
	if(add){
		reasons.push_back(propinfo);

		if(caseone){
			stop = isFalsified(agg, min, max);
		}else{
			stop = isSatisfied(agg, min, max);
		}
	}
}
bool comparePropagationInfoByWeights(const PropagationInfo& one, const PropagationInfo& two) {
	return one.getWeight() < two.getWeight();
}
void SPFWAgg::getExplanation(litlist& lits, const AggReason& ar) {
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	bool caseone = false;
	if(ar.isHeadReason()){
		caseone = head!=ar.getPropLit();
	}else{
		caseone = value(head)==l_True;
	}

	Weight min, max;
	min = getSet().getType().getMinPossible(getSet());
	max = getSet().getType().getMaxPossible(getSet());

	if(!ar.isHeadReason()){
		addValue(getSet().getType(), ar.getPropWeight(), !ar.isInSet(), min, max);
		lits.push_back(value(head)==l_True?not head:head);
	}

	bool stop = false;
	vector<PropagationInfo> reasons;
	if(caseone){
		stop = isFalsified(agg, min, max);
	}else{
		stop = isSatisfied(agg, min, max);
	}

	// FIXME cleanup and add to other explanations
	PCSolver& pcsolver = getSet().getPCSolver();
	const int declevel = pcsolver.getCurrentDecisionLevel();
	bool foundpropagatedlit = false;
	if(pcsolver.modes().currentlevelfirstinexplanation && getTrail().back()->level==declevel){
		for (vprop::const_iterator i = getTrail().back()->props.cbegin(); !stop && !foundpropagatedlit && i < getTrail().back()->props.cend(); ++i) {
			const Lit& lit = i->getLit();
			assert(pcsolver.getLevel(var(lit))==declevel);
			if(lit==ar.getPropLit()){ //NOTE: We only see a subset of the possibly relevant literals, so we are not guaranteed to find the full explanation before seeing the propagated literal, so we have to redo the loop later on.
				foundpropagatedlit = true;
				break;
			}
			if(i->getType()==HEAD){
				continue;
			}

			checkAddToExplan(stop, min, max, *i, agg, caseone, reasons);
		}
	}

	//IMPORTANT: first go over all literals and check which are already in the currently generated partial nogood (only if generating explanation on conflict)
	if(getSet().modes().aggclausesaving==2 && pcsolver.modes().innogoodfirstinexplanation){
		bool foundpropagatedlit = false;
		for(vector<FWTrail*>::const_iterator a=getTrail().cbegin(); !stop && !foundpropagatedlit && a<getTrail().cend(); ++a){
			for (vprop::const_iterator i = (*a)->props.cbegin(); !stop && !foundpropagatedlit && i < (*a)->props.cend(); ++i) {
				const Lit& lit = i->getLit();
				if(lit==ar.getPropLit()){ //NOTE: We only see a subset of the possibly relevant literals, so we are not guaranteed to find the full explanation before seeing the propagated literal, so we have to redo the loop later on.
					foundpropagatedlit = true;
					break;
				}
				if(i->getType()==HEAD){
					continue;
				}

				bool add = true;
				if(pcsolver.modes().currentlevelfirstinexplanation && pcsolver.getLevel(var(lit))==declevel){
					add = false;
				}
				if(!pcsolver.isAlreadyUsedInAnalyze(lit)){
					add = false;
				}

				if(add){
					checkAddToExplan(stop, min, max, *i, agg, caseone, reasons);
				}
			}
		}
	}

	//Then go over the trail earliest to latest to add more to the explanation
	foundpropagatedlit = false;
	for(vector<FWTrail*>::const_iterator a=getTrail().cbegin(); !stop && !foundpropagatedlit && a<getTrail().cend(); ++a){
		for (vprop::const_iterator i = (*a)->props.cbegin(); !stop && !foundpropagatedlit && i < (*a)->props.cend(); ++i) {
			const Lit& lit = i->getLit();
			if(lit==ar.getPropLit()){ //NOTE: We only see a subset of the possibly relevant literals, so we are not guaranteed to find the full explanation before seeing the propagated literal, so we have to redo the loop later on.
				foundpropagatedlit = true;
				break;
			}
			if(i->getType()==HEAD){
				continue;
			}
			bool add = true;
			if(pcsolver.modes().currentlevelfirstinexplanation && pcsolver.getLevel(var(lit))==declevel){
				add = false;
			}
			if(getSet().modes().aggclausesaving==2
					&& pcsolver.modes().innogoodfirstinexplanation
					&& pcsolver.isAlreadyUsedInAnalyze(lit)){
				add = false;
			}

			if(add){
				checkAddToExplan(stop, min, max, *i, agg, caseone, reasons);
			}
		}
	}

	assert(stop);

	//Subsetminimization
	if(getSet().modes().subsetminimizeexplanation){
		sort(reasons.begin(), reasons.end(), compareByWeights<PropagationInfo>);
		for(auto i=reasons.begin(); i<reasons.end(); ++i){
			bool inset = i->getType()==POS;
			removeValue(getSet().getType(), i->getWeight(), inset, min, max);
			if((caseone && isFalsified(agg, min, max) ) ||(!caseone && isSatisfied(agg, min, max))){
				i = reasons.erase(i);
				i--;
			}else{
				break;
			}
		}
	}

	for(auto i=reasons.cbegin(); i<reasons.cend(); ++i){
		lits.push_back(not i->getLit());
	}
}

/*****************
 * MAX AGGREGATE *
 *****************/

MaxFWAgg::MaxFWAgg(TypedSet* set) :
	FWAgg(set) {
}

void MaxFWAgg::initialize(bool& unsat, bool& sat) {
	FWAgg::initialize(unsat, sat);
}

void MaxFWAgg::addToCertainSet(const WL& l) {
	if (l.getWeight() > getCC()) {
		setCC(l.getWeight());
	}
}

void MaxFWAgg::removeFromPossibleSet(const WL& l) {
	TypedSet& set = getSet();
	if (l.getWeight() == getCP()) {
		bool found = false;
		for (vsize i=0; i<set.getWL().size(); ++i) { //INVARIANT: sorted
			if (value(set.getWL()[i].getLit()) != l_False) {
				setCP(set.getWL()[i].getWeight());
				found = true;
			}
		}
		if (!found) { //All literals false: current best is minimal value
			setCP(set.getType().getMinPossible(set));
		}
	}
}

/**
 * head is true  && AGG <= B:
 * 		make all literals false with weight larger than bound
 * head is false && A <= AGG:
 * 		make all literals false with weight larger/eq than bound
 */
/**
 * Returns non-owning pointer
 */
rClause MaxFWAgg::propagateSpecificAtEnd(const Agg& agg, bool headtrue) {
	//if(nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1){ return nullPtrClause; }

	rClause confl = nullPtrClause;
	if (headtrue && agg.hasUB()) {
		for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
					< getSet().getWL().rend() && agg.getCertainBound() < i->getWeight(); ++i) {
			confl = getSet().notifySolver(new SetLitReason(agg, i->getLit(), i->getWeight(), false));
		}
	} else if (!headtrue && agg.hasLB()) {
		for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
					< getSet().getWL().rend() && agg.getCertainBound() <= i->getWeight(); ++i) {
			confl = getSet().notifySolver(new SetLitReason(agg, i->getLit(), i->getWeight(), false));
		}
	}
	if (confl == nullPtrClause) {
		confl = propagateAll(agg, headtrue);
	}
	return confl;
}

/**
 * If only one value is still possible and the head has already been derived, then this last literal
 * might also be propagated, if the constraint is NOT YET SATISFIED!!!
 *
 * head is true  && A <= AGG: Last literal has to be true
 * head is true  && AGG <= B: No conclusion possible (emptyset is also a solution)
 * head is false && A <= AGG: No conclusion possible (emptyset is also a solution)
 * head is false && AGG <= B: Last literal has to be true
 */
/**
 * Returns non-owning pointer
 */
rClause MaxFWAgg::propagateAll(const Agg& agg, bool headtrue) {
	rClause confl = nullPtrClause;

//	if(nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1){ return confl; }

	if ((!agg.hasLB() && headtrue) || (!agg.hasUB() && !headtrue)) {
		return confl;
	}

	Lit l = mkPosLit(0);
	Weight w(0);
	int found = 0;
	for (vwl::const_iterator i=getSet().getWL().cbegin(); found<2 && i<getSet().getWL().cend(); ++i) {
		const WL& wl = (*i);
		if(headtrue){
			if(agg.hasLB() && wl.getWeight() < agg.getCertainBound()){
				continue;
			}
			if(agg.hasUB() && wl.getWeight() > agg.getCertainBound()){
				continue;
			}
		}else{ //headfalse
			if((!agg.hasLB() || wl.getWeight() >= agg.getCertainBound()) &&
				(!agg.hasUB() || wl.getWeight() <= agg.getCertainBound())){
				continue;
			}
		}

		if (value(wl.getLit()) == l_Undef) {
			++found;
			l = wl.getLit();
			w = wl.getWeight();
		} else if (value(wl.getLit()) == l_True) {
			found=2; //hack to stop immediately, because no propagation necessary
		}
	}
	if (found==1) {
		confl = getSet().notifySolver(new SetLitReason(agg, l, w, true));
	}
	return confl;
}

void MaxFWAgg::getExplanation(litlist& lits, const AggReason& ar) {
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	bool search = true, one, inset = false;
	Weight bound = agg.getCertainBound();
	if(!ar.isHeadReason()){
		lits.push_back(value(head)==l_True ? ~head : head);
		if(value(head)==l_True){
			if(agg.hasLB()){
				//all OTHERS larger or eq to bound
				one = false;
			}else{//UB
				search = false;
			}
		}else{//head false
			if(agg.hasLB()){
				search = false;
			}else{//UB
				//all OTHERS larger than bound
				one = false;
				bound+=1;
			}
		}
	}else{
		if(value(head)==l_True){
			if(agg.hasLB()){
				//find one larger or eq and inset
				one = true;
				inset = true;
			}else{//UB
				//all larger than bound
				one = false;
				bound += 1;
			}
		}else{//head false
			if(agg.hasLB()){
				//all larger or eq than bound
				one = false;
			}else{//UB
				//find one larger and inset
				inset = true;
				one = true;
				bound += 1;
			}
		}
	}
	if(search){
		bool found = false;
		for(vector<FWTrail*>::const_iterator a=getTrail().cbegin(); !found && a<getTrail().cend(); ++a){
        	for (vprop::const_iterator i = (*a)->props.cbegin(); !found && i < (*a)->props.cend(); ++i) {
        		if(i->getType()==HEAD || var(i->getLit())==var(ar.getPropLit())){
        			continue;
        		}
        		if(i->getWeight()<bound){
        			continue;
        		}
        		if(inset && i->getType()==NEG){
        			continue;
        		}
        		lits.push_back(~i->getLit());
        		if(one){
        			found = true;
        		}
        	}
		}
	}
}

///////
// SP AGG
///////

SPFWAgg::SPFWAgg(TypedSet* set) :
	FWAgg(set) {
}

void SPFWAgg::addToCertainSet(const WL& l) {
	setCC(getSet().getType().add(getCC(), l.getWeight()));
}

void SPFWAgg::removeFromPossibleSet(const WL& l) {
	setCP(getSet().getType().removeMax(getCP(), l.getWeight()));
}

/**
 * if headtrue && lb => make all literals true with weight > (CP - lb)
 * 				  ub => make all literals false with weight > (ub - CC)
 * if !headtrue && lb => make all literals false with weight > (lb - CC)
 * 				   ub => make all literals true with weight > (CP - ub)
 * if both bounds: do both for headtrue
 * 					do none for headfalse until cc >= lb or cp <= ub
 */
rClause SPFWAgg::propagateSpecificAtEnd(const Agg& agg, bool headtrue) {
	rClause c = nullPtrClause;
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return nullPtrClause;
	//}

	TypedSet& set = getSet();
	const vwl& wls = set.getWL();
	vwl::const_iterator from = wls.cend();
	Weight weightbound;

	bool ub = agg.hasUB();
	const Weight& bound = agg.getCertainBound();
	//determine the lower bound of which weight literals to consider
	const AggProp& type = getSet().getType();
	if (headtrue) {
		if (ub) {
			weightbound = type.removeMin(bound, getCC());
			//+1 because larger and not eq
			if (type.add(weightbound, getCC()) >= bound) {
				weightbound += 1;
			}
		} else {
			weightbound = type.removeMax(getCP(), bound);
			//+1 because larger and not eq
			if (type.add(weightbound, bound) <= getCP()) {
				weightbound += 1;
			}
		}
	} else { //head false
		if (ub) {
			weightbound = type.removeMax(getCP(), bound);
		} else {
			weightbound = type.removeMin(bound, getCC());
		}
	}

#ifdef NOARBITPREC
	if(weightbound == posInfinity() || weightbound == negInfinity()) {
		return c;
	}
#endif

	from = lower_bound(wls.cbegin(), wls.cend(), weightbound);
	if (from == getSet().getWL().cend()) {
		return c;
	}

	/**
	 * The lower bound indicates from which bound all literals should be propagate that are not yet known to the aggregate solver
	 * All literals known to the sat solver are certainly sa
	 */
	for (vwl::const_iterator u = from; c == nullPtrClause && u < wls.cend(); ++u) {
		const Lit& l = (*u).getLit();

		bool propagate = value(l)==l_Undef;

		if(!propagate && getSet().getPCSolver().getLevel(var(l))==getSet().getPCSolver().getCurrentDecisionLevel()){
			bool found = false;
			for(vprop::const_iterator i=getTrail().back()->props.cbegin(); !found && i<getTrail().back()->props.cend(); ++i){
				if(var(l)==var(i->getLit())){
					found = true;
				}
			}
			propagate = !found;
		}

		//Only propagate those that are not already known in the aggregate solver!
		if (propagate) {
			if ((agg.hasUB() && headtrue) || (!agg.hasUB() && !headtrue)) {
				c = getSet().notifySolver(new SetLitReason(agg, (*u).getLit(), (*u).getWeight(), false));
			} else {
				c = getSet().notifySolver(new SetLitReason(agg, (*u).getLit(), (*u).getWeight(), true));
			}
		}
	}

	//TODO the looping over the trail is TOO slow! compared to old card
	//TODO but bigger problem is that he keeps on deriving the same propagations!
	//=> add a check that does not do propagations if the derived weight bound is the same
	//=> add a check that if only cp or cc is adapted, only aggs with such bound are checked!

#ifdef DEBUG
	bool allknown = true;
	for (vwl::const_iterator u = wls.cbegin(); allknown && u < wls.cend(); ++u) {
		if((*u).getWeight()>=weightbound && value((*u).getLit())==l_Undef){
			allknown = false;
		}
	}
	assert(c!=nullPtrClause || allknown);
#endif

	return c;
}

SumFWAgg::SumFWAgg(TypedSet* set)
	: SPFWAgg(set) {

}

void SumFWAgg::initialize(bool& unsat, bool& sat) {
	unsat = false;
	if (getSet().getAgg().size() == 0) {
		sat = true;
		return;
	}

#ifdef NOARBITPREC
	//Test whether the total sum of the weights is not infinity for intweights
	Weight total(0);
	for(vwl::const_iterator i=getSet().getWL().cbegin(); i<getSet().getWL().cend(); ++i) {
		if(INT_MAX-total < i->getWeight()) {
			throw idpexception("The total sum of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total += abs(i->getWeight());
	}
#endif

	//Calculate the total negative weight to make all weights positive
	vwl wlits2;
	Weight totalneg(0);
	for (vwl::const_iterator i = getSet().getWL().cbegin(); i < getSet().getWL().cend(); ++i) {
		if (i->getWeight() < 0) {
			totalneg -= i->getWeight();
		}
	}
	if (totalneg > 0) {
		//Important: negate literals of with negative weights!
		for (vwl::const_iterator i = getSet().getWL().cbegin(); i < getSet().getWL().cend(); ++i) {
			if(i->getWeight()<0){
				wlits2.push_back(WL(~i->getLit(), abs(i->getWeight())));
			}else{
				wlits2.push_back(*i);
			}
		}
		getSet().setWL(wlits2);
		for (auto i = getSet().getAgg().cbegin(); i < getSet().getAgg().cend(); ++i) {
			Weight b = getSet().getType().add((*i)->getCertainBound(), totalneg);
			(*i)->setBound(AggBound((*i)->getSign(), b));
		}
	}

	FWAgg::initialize(unsat, sat);
}

ProdFWAgg::ProdFWAgg(TypedSet* set) :
	SPFWAgg(set) {
}

void ProdFWAgg::initialize(bool& unsat, bool& sat) {
	unsat = false;
	if (getSet().getAgg().size() == 0) {
		sat = true;
		return;
	}
	for (auto i = getSet().getAggNonConst().begin(); i < getSet().getAggNonConst().end(); ++i) {
		if((*i)->getCertainBound()<=0){
			if((*i)->getSign()==AGGSIGN_LB){
				// always positive
				delete(*i);
				getSet().getAggNonConst().erase(i);
				i--;
			}else{
				unsat = true;
				return;
			}
		}
	}
#ifdef NOARBITPREC
	//Test whether the total product of the weights is not infinity for intweights
	Weight total(1);
	for(auto i=getSet().getWL().cbegin(); i<getSet().getWL().cend(); ++i) {
		if(posInfinity()/total < i->getWeight()) {
			throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total *= i->getWeight();
	}
#endif

	FWAgg::initialize(unsat, sat);
}
