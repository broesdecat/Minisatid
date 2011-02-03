#include "modules/aggsolver/FullyWatched.hpp"

#include "modules/aggsolver/AggPrint.hpp"
#include "modules/AggSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace std;
using namespace MinisatID;
using namespace Aggrs;

typedef Agg* pagg;
typedef Watch* pw;

FWAgg::FWAgg(TypedSet* set) :
	Propagator(set) {

}

void FWAgg::initialize(bool& unsat, bool& sat) {
	if (getSet().getAgg().size() == 0) {
		sat = true;	return;
	}

	trail.push_back(new FWTrail(0, 0, 0));
	setCP(getSet().getBestPossible());
	setCC(getSet().getType().getESV());

	int counter = 0;
	for (vpagg::iterator i = getSet().getAggNonConst().begin(); !unsat && i < getSet().getAggNonConst().end();) {
		pagg agg = (*i);
		lbool result = initialize(*agg);
		if (result == l_True && !agg->isDefined()) {
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			//BUT ONLY if it is not defined (or at a later stage, if it cannot be in any loop)
			getSolver()->removeHeadWatch(var(agg->getHead()));
			i = getSet().getAggNonConst().erase(i);
			continue;
		} else if (result == l_False) {
			unsat = true; //UNSAT because always false
			return;
		}
		agg->setIndex(counter++);
		i++;
	}

	if(getSet().getAgg().size()==0){
		sat = true; return;
	}

	for (vwl::const_iterator j = getSet().getWL().begin(); j < getSet().getWL().end(); j++) {
		const Lit& l = (*j).getLit();
		Var v = var(l);
		getSolver()->addPermWatch(v, new Watch(getSetp(), *j));
	}

	Propagator::initialize(unsat, sat);
}

/**
 * Returns true if this aggregate can be propagated in the initialization, so it will never change truth value
 * and can be left out of any propagations.
 * Returns false if the aggregate is certainly unsat.
 */
lbool FWAgg::initialize(const Agg& agg) {
	rClause confl = nullPtrClause;
	if(agg.isOptim()){
		return l_Undef;
	}

	Expl basedon = HEADONLY;
	lbool hv = canPropagateHead(agg, getCC(), getCP(), basedon);
	bool alwaystrue = false;
	if (hv != l_Undef && !agg.isOptim()) {
		alwaystrue = true;
		//reportf("No more propagations for %d", getPrintableVar(var(head)));
	}
	if (hv == l_True) {
		confl = getSolver()->notifySolver(new HeadReason(agg, basedon, agg.getHead()));
	} else if (hv == l_False) {
		confl = getSolver()->notifySolver(new HeadReason(agg, basedon, ~agg.getHead()));
	}
	if (confl != nullPtrClause) {
		return l_False;
	}

	return alwaystrue ? l_True : l_Undef;
}

void FWAgg::backtrack(int nblevels, int untillevel){
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
rClause FWAgg::propagate(int level, const Agg& agg, bool headtrue) {
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return nullPtrClause;
	//}

	FWTrail* fwobj = getTrail().back();
	if(fwobj->level<level){
		getTrail().push_back(new FWTrail(level, fwobj->CBC, fwobj->CBP));
		fwobj = getTrail().back();
		getSolver()->addToBackTrail(getSetp());
	}

	if(fwobj->start == fwobj->props.size()){
		getSolver()->addToPropTrail(getSetp());
	}

	fwobj->props.push_back(PropagationInfo(headtrue?agg.getHead():~agg.getHead(), 0, HEAD));
	fwobj->headindex.push_back(agg.getIndex());
	fwobj->headtime.push_back(fwobj->props.size());

	return nullPtrClause;
}

rClause FWAgg::propagate(const Lit& p, pw ws, int level) {
	FWTrail* fwobj = getTrail().back();
	if(fwobj->level<level){
		getTrail().push_back(new FWTrail(level, fwobj->CBC, fwobj->CBP));
		fwobj = getTrail().back();
		getSolver()->addToBackTrail(getSetp());
	}
	if(fwobj->start == fwobj->props.size()){
		getSolver()->addToPropTrail(getSetp());
	}

#ifdef DEBUG
	bool found = false;
	for(vector<TypedSet*>::const_iterator i=getSolver()->getPropTrail().begin(); !found && i<getSolver()->getPropTrail().end(); i++){
		if(getSetp()==*i){
			found = true;
		}
	}
	assert(found);
#endif

	fwobj->props.push_back(PropagationInfo(p, ws->getWL().getWeight(), ws->getType(p)));

	return nullPtrClause;
}

rClause FWAgg::propagateAtEndOfQueue(int level){
	rClause confl = nullPtrClause;

	FWTrail& fwobj = *getTrail().back();

	assert(fwobj.level==level && fwobj.start!=fwobj.props.size());

	bool changedcp = false;
	bool changedcc = false;
	for(uint i=fwobj.start; i<fwobj.props.size(); i++){
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

	for(vector<int>::const_iterator i=fwobj.headindex.begin(); confl==nullPtrClause && i<fwobj.headindex.end(); i++){
		pagg agg = getSet().getAgg()[*i];
		assert(agg->getSet()->getAgg()[agg->getIndex()]==agg && *i == agg->getIndex());
		lbool headval = value(agg->getHead());
		assert(headval!=l_Undef);
		confl = propagateSpecificAtEnd(*agg, headval==l_True);
	}

	if(changedcc || changedcp){
		for (vpagg::const_iterator i = getSet().getAgg().begin(); confl == nullPtrClause && i<getSet().getAgg().end(); i++){
			const Agg& pa = **i;

			if (getSolver()->verbosity() >= 6) {
				report("Propagating into aggr: ");
				Aggrs::print(getSolver()->verbosity(), pa, false);
				report(", CC = %s, CP = %s\n", toString(getCC()).c_str(), toString(getCP()).c_str());
			}

			lbool hv = value(pa.getHead());

			//FIXME dansmee problem should not occur when not using asapaggprop?

			//FIXME ugly
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

			Expl basedon = HEADONLY;
			lbool result = canPropagateHead(pa, getCC(), getCP(), basedon);
			if(hv!=l_Undef){
				if(result==l_Undef){
					confl = propagateSpecificAtEnd(pa, hv == l_True);
				}else if(hv!=result){
					confl = getSolver()->notifySolver(new HeadReason(pa, basedon, result==l_True?pa.getHead():~pa.getHead()));
				}
			}else if(result!=l_Undef){
				confl = getSolver()->notifySolver(new HeadReason(pa, basedon, result==l_True?pa.getHead():~pa.getHead()));
			}
		}
	}

	return confl;
}

lbool Aggrs::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP, Expl& basedon) {
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return headvalue[agg.getIndex()];
	//}

	lbool result = l_Undef;

	//add if derived: headproptime[agg.getIndex()] = getStack().size();
	const Weight& b = agg.getCertainBound();
	if(agg.hasUB()){
		if(CC > b){
			basedon = BASEDONCC;
			result = l_False;
		}else if(CP <= b){
			basedon = BASEDONCP;
			result = l_True;
		}
	}else{
		if(CC>= b){
			basedon = BASEDONCC;
			result = l_True;
		}else if(CP < b){
			basedon = BASEDONCP;
			result = l_False;
		}
	}

	return result;
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */

inline bool isSatisfied(bool headtrue, const Weight& current, bool cc, bool ub, const Weight& bound) {
	if(headtrue && ub){
		return (cc && current <= bound) || (!cc && current>bound);
	}else if(headtrue && !ub){
		return (cc && current >= bound) || (!cc && current<bound);
	}else if(!headtrue && ub){
		return (!cc && current > bound) || (cc && current<=bound);
	}else if(!headtrue && !ub){
		return (!cc && current < bound) || (cc && current>=bound);
	}
	assert(false);
	return false;
}

void SPFWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	bool headtrue = value(head)==l_True;
	if(ar.isHeadReason()){
		headtrue = ar.getPropLit()==head;
	}

	bool mono = (ar.getExpl()==BASEDONCC && !headtrue) ||
				(ar.getExpl()==BASEDONCP && headtrue);
	bool inset = ar.getExpl()==BASEDONCP;

	Weight min, max;
	if(!agg.hasUB()){
		min = getSetp()->getType().getESV(); max = getSet().getType().getBestPossible(getSetp());
	}else{
		min = getSet().getType().getBestPossible(getSetp()); max = getSetp()->getType().getESV();
	}

	if(!ar.isHeadReason()){
		if(mono){
			min = getSet().getType().add(min, ar.getPropWeight());
			max = getSet().getType().remove(max, ar.getPropWeight());
		}else{
			min = getSet().getType().remove(min, ar.getPropWeight());
			max = getSet().getType().add(max, ar.getPropWeight());
		}
		lits.push(headtrue?~head:head);
	}

	//check monotone that are false when monotone became true, a-m became false or head became false
	bool checkmonofalse = (ar.isHeadReason() && !headtrue) || (!ar.isHeadReason() && ((mono && inset) || (!mono && !inset)));

	bool ub = agg.hasUB();
	const Weight& bound = agg.getCertainBound();
	bool satisfied = false;
	vector<WL> reasons;
	if(checkmonofalse){
		satisfied = isSatisfied(headtrue, max, false, ub, bound);
		for(vector<FWTrail*>::const_iterator a=getTrail().begin(); !satisfied && a<getTrail().end(); a++){
        	for (vprop::const_iterator i = (*a)->props.begin(); !satisfied && i < (*a)->props.end(); i++) {
				bool monolit = getSet().getType().isMonotone(agg, (*i).getWL());
				if((monolit && (*i).getType()==NEG) || (!monolit && (*i).getType()==POS)){
					reasons.push_back((*i).getWL());
					if(monolit){
						max = getSet().getType().remove(max, (*i).getWeight());
					}else{
						max = getSet().getType().add(max, (*i).getWeight());
					}
					satisfied = isSatisfied(headtrue, max, false, ub, bound);
				}
        	}
		}
	}else{
		satisfied = isSatisfied(headtrue, min, true, ub, bound);
		for(vector<FWTrail*>::const_iterator a=getTrail().begin(); !satisfied && a<getTrail().end(); a++){
        	for (vprop::const_iterator i = (*a)->props.begin(); !satisfied && i < (*a)->props.end(); i++) {
				bool monolit = getSet().getType().isMonotone(agg, (*i).getWL());
				if((monolit && (*i).getType()==POS) || (!monolit && (*i).getType()==NEG)){
					reasons.push_back((*i).getWL());
					if(monolit){
						min = getSet().getType().add(min, (*i).getWeight());
					}else{
						min = getSet().getType().remove(min, (*i).getWeight());
					}
					satisfied = isSatisfied(headtrue, min, true, ub, bound);
				}
        	}
		}
	}

	assert(satisfied);

	//Subsetminimization
	//Slowdown for weight bounded set
	if(getSolver()->modes().subsetminimizeexplanation){
		bool changes = true;
		if(checkmonofalse){
			while(changes){
				changes = false;
				for(vector<WL>::iterator i=reasons.begin(); i<reasons.end(); i++){
					Weight temp = max;

					bool monolit = getSet().getType().isMonotone(agg, *i);
					if(monolit){
						max = getSet().getType().add(max, (*i).getWeight());
					}else{
						max = getSet().getType().remove(max, (*i).getWeight());
					}

					if(isSatisfied(headtrue, max, false, agg.hasUB(), agg.getCertainBound())){
						reasons.erase(i);
						changes = true;
					}else{
						max = temp;
					}
				}
			}
		}else{
			while(changes){
				changes = false;
				for(vector<WL>::iterator i=reasons.begin(); i<reasons.end(); i++){
					Weight temp = min;

					bool monolit = getSet().getType().isMonotone(agg, *i);
					if(monolit){
						min = getSet().getType().remove(min, (*i).getWeight());
					}else{
						min = getSet().getType().add(min, (*i).getWeight());
					}

					if(isSatisfied(headtrue, min, true, agg.hasUB(), agg.getCertainBound())){
						reasons.erase(i);
						changes = true;
					}else{
						min = temp;
					}
				}
			}
		}
	}

	for(vector<WL>::const_iterator i=reasons.begin(); i<reasons.end(); i++){
		lits.push(~(*i).getLit());
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
		for (vsize i=0; i<set.getWL().size(); i++) {
			if (value(set.getWL()[i].getLit()) != l_False) {
				setCP(set.getWL()[i].getWeight());
				found = true;
			}
		}
		if (!found) {
			setCP(set.getType().getESV());
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
					< getSet().getWL().rend() && agg.getCertainBound() < (*i).getWeight(); i++) {
			confl = getSolver()->notifySolver(new SetLitReason(agg, (*i).getLit(), (*i).getWeight(), HEADONLY, false));
		}
	} else if (!headtrue && agg.hasLB()) {
		for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
					< getSet().getWL().rend() && agg.getCertainBound() <= (*i).getWeight(); i++) {
			confl = getSolver()->notifySolver(new SetLitReason(agg, (*i).getLit(), (*i).getWeight(), HEADONLY, false));
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

	Lit l = mkLit(0);
	Weight w(0);
	int found = 0;
	for (vwl::const_iterator i=getSet().getWL().begin(); found<2 && i<getSet().getWL().end(); i++) {
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
			found++;
			l = wl.getLit();
			w = wl.getWeight();
		} else if (value(wl.getLit()) == l_True) {
			found=2; //hack to stop immediately, because no propagation necessary
		}
	}
	if (found==1) {
		//basedon is not really relevant for max
		confl = getSolver()->notifySolver(new SetLitReason(agg, l, w, BASEDONCC, true));
	}
	return confl;
}

void MaxFWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	bool search = true, one, inset = false;
	Weight bound = agg.getCertainBound();
	if(!ar.isHeadReason()){
		lits.push(value(head)==l_True ? ~head : head);
		if(value(head)==l_True){
			if(agg.hasLB()){
				//all others larger or eq to bound
				one = false;
			}else{//UB
				search = false;
			}
		}else{//head false
			if(agg.hasLB()){
				search = false;
			}else{//UB
				//all others larger than bound
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
		for(vector<FWTrail*>::const_iterator a=getTrail().begin(); !found && a<getTrail().end(); a++){
        	for (vprop::const_iterator i = (*a)->props.begin(); !found && i < (*a)->props.end(); i++) {
        		if((*i).getWeight()<bound){
        			continue;
        		}
        		if(inset && (*i).getType()==NEG){
        			continue;
        		}
        		lits.push(~(*i).getLit());
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
	setCP(getSet().getType().remove(getCP(), l.getWeight()));
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
	vwl::const_iterator from = wls.end();
	Weight weightbound;

	bool ub = agg.hasUB();
	const Weight& bound = agg.getCertainBound();
	Expl basedon;
	//determine the lower bound of which weight literals to consider
	const AggProp& type = getSet().getType();
	if (headtrue) {
		if (ub) {
			basedon = BASEDONCC;
			weightbound = type.remove(bound, getCC());
			//+1 because larger and not eq
			if (type.add(weightbound, getCC()) == bound) {
				weightbound += 1;
			}
		} else {
			basedon = BASEDONCP;
			weightbound = type.remove(getCP(), bound);
			//+1 because larger and not eq
			if (type.add(weightbound, bound) == getCP()) {
				weightbound += 1;
			}
		}
	} else { //head false
		if (ub) {
			basedon = BASEDONCP;
			weightbound = type.remove(getCP(), bound);
		} else {
			basedon = BASEDONCC;
			weightbound = type.remove(bound, getCC());
		}
	}

#ifdef NOARBITPREC
	if(weightbound == posInfinity() || weightbound == negInfinity()) {
		return c;
	}
#endif

	from = lower_bound(wls.begin(), wls.end(), weightbound);
	if (from == getSet().getWL().end()) {
		return c;
	}

	/**
	 * The lower bound indicates from which bound all literals should be propagate that are not yet known to the aggregate solver
	 * All literals known to the sat solver are certainly sa
	 */
	for (vwl::const_iterator u = from; c == nullPtrClause && u < wls.end(); u++) {
		const Lit& l = (*u).getLit();

		bool propagate = value(l)==l_Undef;

		if(!propagate && getSolver()->getPCSolver()->getLevel(var(l))==getSolver()->getPCSolver()->getCurrentDecisionLevel()){
			bool found = false;
			for(vprop::const_iterator i=getTrail().back()->props.begin(); !found && i<getTrail().back()->props.end(); i++){
				if(var(l)==var((*i).getLit())){
					found = true;
				}
			}
			propagate = !found;
		}

		//Only propagate those that are not already known in the aggregate solver!
		if (propagate) {
			if ((agg.hasUB() && headtrue) || (!agg.hasUB() && !headtrue)) {
				c = getSolver()->notifySolver(new SetLitReason(agg, (*u).getLit(), (*u).getWeight(), basedon, false));
			} else {
				c = getSolver()->notifySolver(new SetLitReason(agg, (*u).getLit(), (*u).getWeight(), basedon, true));
			}
		}
	}

	//FIXME the looping over the trail is TOO slow! compared to old card
	//FIXME but bigger problem is that he keeps on deriving the same propagations!
	//=> add a check that does not do propagations if the derived weight bound is the same
	//=> add a check that if only cp or cc is adapted, only aggs with such bound are checked!

#ifdef DEBUG
	bool allknown = true;
	for (vwl::const_iterator u = wls.begin(); allknown && u < wls.end(); u++) {
		if((*u).getWeight()>=weightbound && getSolver()->value((*u).getLit())==l_Undef){
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
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); i++) {
		if(INT_MAX-total < (*i).getWeight()) {
			throw idpexception("The total sum of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total += abs((*i).getWeight());
	}
#endif

	//Calculate the total negative weight to make all weights positive
	vwl wlits2;
	Weight totalneg(0);
	for (vwl::const_iterator i = getSet().getWL().begin(); i < getSet().getWL().end(); i++) {
		if ((*i).getWeight() < 0) {
			totalneg -= (*i).getWeight();
		}
	}
	if (totalneg > 0) {
		//Important: negate literals of with negative weights!
		for (vwl::const_iterator i = getSet().getWL().begin(); i < getSet().getWL().end(); i++) {
			if((*i).getWeight()<0){
				wlits2.push_back(WL(~(*i).getLit(), abs((*i).getWeight())));
			}else{
				wlits2.push_back(*i);
			}
		}
		getSet().setWL(wlits2);
		for (vpagg::const_iterator i = getSet().getAgg().begin(); i < getSet().getAgg().end(); i++) {
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
#ifdef NOARBITPREC
	//Test whether the total product of the weights is not infinity for intweights
	Weight total(1);
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); i++) {
		if(posInfinity()/total < (*i).getWeight()) {
			throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total *= (*i).getWeight();
	}
#endif

	FWAgg::initialize(unsat, sat);
}
