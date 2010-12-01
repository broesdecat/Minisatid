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
		sat = true;
		return;
	}
	//truth.resize(getSet().getWL().size(), l_Undef);

	trail.push_back(FWTrail(0, 0, 0));
	setCP(getSet().getBestPossible());
	setCC(getSet().getESV());

	int counter = 0;
	for (vpagg::iterator i = getSet().getAggNonConst().begin(); !unsat && i < getSet().getAggNonConst().end();) {
		pagg agg = (*i);
		lbool result = initialize(*agg);
		if (result == l_True && !agg->isDefined()) {
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			//BUT ONLY if it is not defined (or at a later stage, if it cannot be in any loop)
			getSet().getSolver()->removeHeadWatch(var(agg->getHead()));
			i = getSet().getAggNonConst().erase(i);
			continue;
		} else if (result == l_False) {
			unsat = true; //UNSAT because always false
			return;
		}
		agg->setIndex(counter++);
		i++;
	}

	for (vsize j = 0; j < getSet().getWL().size(); j++) {
		const Lit& l = getSet().getWL()[j].getLit();
		Var v = var(l);
		getSet().getSolver()->addPermWatch(v, new Watch(getSetp(), j, true, sign(l)?false:true));
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

	Expl basedon;
	lbool hv = canPropagateHead(agg, getCC(), getCP(), basedon);
	bool alwaystrue = false;
	if (hv != l_Undef && !agg.isOptim()) {
		alwaystrue = true;
		//reportf("No more propagations for %d", gprintVar(var(head)));
	}
	if (hv == l_True) {
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, agg.getHead(), 0, true));
	} else if (hv == l_False) {
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, ~agg.getHead(), 0, true));
	}
	if (confl != nullPtrClause) {
		return l_False;
	}

	return alwaystrue ? l_True : l_Undef;
}

void FWAgg::backtrack(int nblevels, int untillevel){
	while(getTrail().back().level>untillevel){
		//report("Backtrack trail of FW\n");
		getTrail().pop_back();
	}
}

/**
 * Returns non-owning pointer
 */
rClause FWAgg::propagate(const Agg& agg, int level) {
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return nullPtrClause;
	//}

	if(getTrail().back().level<level){
		//report("Added trail level, trail level %d, current level %d\n", getTrail().back().level, level);
		getTrail().push_back(FWTrail(level, getTrail().back().CBC, getTrail().back().CBP));
		getSolver()->addToTrail(getSetp());
	}

	lbool headtrue = getSolver()->value(agg.getHead());
	getTrail().back().props.push_back(PropagationInfo(getSolver()->value(agg.getHead())==l_True?agg.getHead():~agg.getHead(), 0, HEAD));
	getTrail().back().headindex.push_back(agg.getIndex());
	getTrail().back().headtime.push_back(getTrail().back().props.size());

	return nullPtrClause;
}

rClause FWAgg::propagate(const Lit& p, pw ws, int level) {
	if(getTrail().back().level<level){
		//report("Added trail level, trail level %d, current level %d\n", getTrail().back().level, level);
		getTrail().push_back(FWTrail(level, getTrail().back().CBC, getTrail().back().CBP));
		getSolver()->addToTrail(getSetp());
	}

	getTrail().back().props.push_back(PropagationInfo(p, ws->getWL().getWeight(), ws->getType(sign(p))));

	return nullPtrClause;
}

rClause FWAgg::propagateAtEndOfQueue(int level){
	//report("Propagate at end\n");
	rClause confl = nullPtrClause;

	if(getTrail().back().level!=level || getTrail().back().start==getTrail().back().props.size()){
		return confl;
	}

	for(uint i=getTrail().back().start; i<getTrail().back().props.size(); i++){
		const PropagationInfo& p = getTrail().back().props[i];
		if(p.getType()!=HEAD){
			WL wl(p.getLit(), p.getWeight());
			//report("Type = %s\n", p.getType()==POS?"pos":"neg");
			p.getType()==POS ? addToCertainSet(wl) : removeFromPossibleSet(wl);
		}
	}
	getTrail().back().start = getTrail().back().props.size();

	//report("Current values: CC=%d and CP=%d\n", getTrail().back().CBC, getTrail().back().CBP);

	for(vector<int>::const_iterator i=getTrail().back().headindex.begin(); confl==nullPtrClause && i<getTrail().back().headindex.end(); i++){
		pagg agg = getSet().getAgg()[*i];
		assert(agg->getSet()->getAgg()[agg->getIndex()]==agg && *i == agg->getIndex());
		lbool headval = getSolver()->value(agg->getHead());
		assert(headval!=l_Undef);
		confl = propagate(*agg, headval==l_True);
	}

/* DOES NOT HOLD, because intermediate propagations can happen without aborting propagation
TODO might abort propagation of next aggregates to first do unit propagation
#ifdef DEBUG
	for (vpagg::const_iterator i = getSet().getAgg().begin(); confl == nullPtrClause && i<getSet().getAgg().end(); i++){
		const Agg& pa = **i;
		bool allknown = true;
		for(int i=0; i<getSet().getWL().size(); i++){
			if(value(getSet().getWL()[i].getLit())==l_Undef){
				allknown = false;
			}
		}
		assert(!allknown || getCC()==getCP());
	}
#endif
*/

	for (vpagg::const_iterator i = getSet().getAgg().begin(); confl == nullPtrClause && i<getSet().getAgg().end(); i++){
		const Agg& pa = **i;

		if (getSet().getSolver()->verbosity() >= 6) {
			report("Propagating into aggr: ");
			Aggrs::print(pa, false);
			report(", CC = %d, CP = %d\n", getCC(), getCP());
		}

		lbool hv = getSolver()->value(pa.getHead());
		Expl basedon;
		lbool result = canPropagateHead(pa, getCC(), getCP(), basedon);
		if(hv!=l_Undef){
			if(result==l_Undef){
				confl = propagate(pa, hv == l_True);
			}else if(hv!=result){
				confl = getSet().getSolver()->notifySolver(new AggReason(pa, basedon, result == l_True ? pa.getHead() : ~pa.getHead(), 0, true));
			}
		}else if(result!=l_Undef){
			confl = getSet().getSolver()->notifySolver(new AggReason(pa, basedon, result == l_True ? pa.getHead() : ~pa.getHead(), 0, true));
		}
	}

	return confl;
}

lbool FWAgg::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP, Expl& basedon) const {
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return headvalue[agg.getIndex()];
	//}

	lbool result = l_Undef;

	if(agg.hasUB() && agg.hasLB()){
		if(CC > agg.getBound().lb){
			basedon = BASEDONCC;
			result = l_False;
		}else if(CP < agg.getBound().ub){
			basedon = BASEDONCP;
			result = l_False;
		}else if(CC >= agg.getBound().ub && CP <= agg.getBound().lb){
			basedon = BASEDONBOTH;
			result = l_True;
		}
	}else{
		//add if derived: headproptime[agg.getIndex()] = getStack().size();
		if(agg.hasUB()){
			if(CC > agg.getBound().ub){
				basedon = BASEDONCC;
				result = l_False;
			}else if(CP <= agg.getBound().ub){
				basedon = BASEDONCP;
				result = l_True;
			}
		}else{
			if(CC>= agg.getBound().lb){
				basedon = BASEDONCC;
				result = l_True;
			}else if(CP < agg.getBound().lb){
				basedon = BASEDONCP;
				result = l_False;
			}
		}
	}

	return result;
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
inline bool isSatisfied(bool headtrue, const Weight& current, bool cc, bool lower, const Weight& bound) {
	if(headtrue && lower){
		return (cc && current <= bound) || (!cc && current>bound);
	}else if(headtrue && !lower){
		return (cc && current >= bound) || (!cc && current<bound);
	}else if(!headtrue && lower){
		return (!cc && current > bound) || (cc && current<=bound);
	}else if(!headtrue && !lower){
		return (!cc && current < bound) || (cc && current>=bound);
	}
	assert(false);
	return false;
}

void SPFWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	//VERY IMPORTANT for conflicts over the head!!!!!
	bool headtrue = getSolver()->value(head)==l_True;
	if(ar.isHeadReason()){
		headtrue = ar.getPropLit()==head;
	}

	bool mono = (ar.getExpl()==BASEDONCC && !headtrue) ||
				(ar.getExpl()==BASEDONCP && headtrue);
	bool inset = ar.getExpl()==BASEDONCP;

	Weight min, max;
	if(!agg.hasUB()){
		min = getSetp()->getESV(); max = getSetp()->getType().getBestPossible(getSetp());
	}else{
		min = getSetp()->getType().getBestPossible(getSetp()); max = getSetp()->getESV();
	}

	if(!ar.isHeadReason()){
		if(mono){
			min = getSetp()->getType().add(min, ar.getPropWeight());
			max = getSetp()->getType().remove(max, ar.getPropWeight());
		}else{
			min = getSetp()->getType().remove(min, ar.getPropWeight());
			max = getSetp()->getType().add(max, ar.getPropWeight());
		}
		lits.push(headtrue?~head:head);
	}

	//check monotone that are false when monotone became true, a-m became false or head became false
	bool checkmonofalse = (ar.isHeadReason() && !headtrue) || (!ar.isHeadReason() && ((mono && inset) || (!mono && !inset)));

	//FIXME solve for two bounds
	bool ub = agg.hasUB();
	const Weight& bound = ub?agg.getBound().ub:agg.getBound().lb;
	bool satisfied = false;
	vector<WL> reasons;
	if(checkmonofalse){
		satisfied = isSatisfied(headtrue, max, false, ub, bound);
		for(vector<FWTrail>::const_iterator a=getTrail().begin(); !satisfied && a<getTrail().end(); a++){
        	for (vprop::const_iterator i = (*a).props.begin(); !satisfied && i < (*a).props.end(); i++) {
				bool monolit = getSetp()->getType().isMonotone(agg, (*i).getWL(), agg.hasUB());
				if((monolit && (*i).getType()==NEG) || (!monolit && (*i).getType()==POS)){
					reasons.push_back((*i).getWL());
					if(monolit){
						max = getSetp()->getType().remove(max, (*i).getWeight());
					}else{
						max = getSetp()->getType().add(max, (*i).getWeight());
					}
					satisfied = isSatisfied(headtrue, max, false, ub, bound);
				}
        	}
		}
	}else{
		satisfied = isSatisfied(headtrue, min, true, ub, bound);
		for(vector<FWTrail>::const_iterator a=getTrail().begin(); !satisfied && a<getTrail().end(); a++){
        	for (vprop::const_iterator i = (*a).props.begin(); !satisfied && i < (*a).props.end(); i++) {
				bool monolit = getSetp()->getType().isMonotone(agg, (*i).getWL(), agg.hasUB());
				if((monolit && (*i).getType()==POS) || (!monolit && (*i).getType()==NEG)){
					reasons.push_back((*i).getWL());
					if(monolit){
						min = getSetp()->getType().add(min, (*i).getWeight());
					}else{
						min = getSetp()->getType().remove(min, (*i).getWeight());
					}
					satisfied = isSatisfied(headtrue, min, true, ub, bound);
				}
        	}
		}
	}

	assert(satisfied);

	//FIXME add option
	//Subsetminimization
	//Mainly slowdown for weight bounded set
/*	bool changes = true;
	int startsize = reasons.size();
	if(checkmonofalse){
		while(changes){
			changes = false;
			for(vector<WL>::iterator i=reasons.begin(); i<reasons.end(); i++){
				Weight temp = max;

				bool monolit = getSetp()->getType().isMonotone(agg, *i);
				if(monolit){
					max = getSetp()->getType().add(max, (*i).getWeight());
				}else{
					max = getSetp()->getType().remove(max, (*i).getWeight());
				}

				if(isSatisfied(headtrue, max, false, agg.hasLB(), agg.getSoloBound())){
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

				bool monolit = getSetp()->getType().isMonotone(agg, *i);
				if(monolit){
					min = getSetp()->getType().remove(min, (*i).getWeight());
				}else{
					min = getSetp()->getType().add(min, (*i).getWeight());
				}

				if(isSatisfied(headtrue, min, true, agg.hasLB(), agg.getSoloBound())){
					reasons.erase(i);
					changes = true;
				}else{
					min = temp;
				}
			}
		}
	}*/

	for(vector<WL>::const_iterator i=reasons.begin(); i<reasons.end(); i++){
		lits.push(~(*i).getLit());
	}

	if(getSolver()->verbosity()>=5){
		report("Explanation for ");
		print(agg, false);
		report("is\n");
		for(int i=0; i<lits.size(); i++){
			report(" "); gprintLit(lits[i]);
		}
		report("\n");
	}
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
void MaxFWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	if (!ar.isHeadReason()) {
		lits.push(getSolver()->isTrue(head) ? ~head : head);
	}else{
		//FIXME
		//lits.push(~ar.getLit());
		for(vector<FWTrail>::const_iterator a=getTrail().begin(); a<getTrail().end(); a++){
        	for (vprop::const_iterator i = (*a).props.begin(); i < (*a).props.end(); i++) {
        		lits.push(~(*i).getLit());
        	}
		}
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
	if (l.getWeight() == getCP()) {
		bool found = false;
		for (vsize i=0; i<getSet().getWL().size(); i++) {
			if (getSolver()->value(getSet().getWL()[i].getLit()) != l_False) {
				setCP(getSet().getWL()[i].getWeight());
				found = true;
			}
		}
		if (!found) {
			setCP(getSet().getESV());
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
rClause MaxFWAgg::propagate(const Agg& agg, bool headtrue) {
	//if(nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1){ return nullPtrClause; }

	rClause confl = nullPtrClause;
	if (headtrue && agg.hasUB()) {
		for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
					< getSet().getWL().rend() && agg.getBound().ub < (*i).getWeight(); i++) {
			confl = getSet().getSolver()->notifySolver(new AggReason(agg, HEADONLY, ~(*i).getLit(), (*i).getWeight()));
		}
	} else if (!headtrue && agg.hasLB()) {
		for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
					< getSet().getWL().rend() && agg.getBound().lb <= (*i).getWeight(); i++) {
			confl = getSet().getSolver()->notifySolver(new AggReason(agg, HEADONLY, ~(*i).getLit(), (*i).getWeight()));
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

	Lit l;
	Weight w;
	int found = 0;
	for (vwl::const_iterator i=getSet().getWL().begin(); found<2 && i<getSet().getWL().end(); i++) {
		const WL& wl = (*i);
		if(headtrue){
			if(agg.hasLB() && wl.getWeight() < agg.getBound().lb){
				continue;
			}
			if(agg.hasUB() && wl.getWeight() > agg.getBound().ub){
				continue;
			}
		}else{ //headfalse
			if((!agg.hasLB() || wl.getWeight() >= agg.getBound().lb) &&
				(!agg.hasUB() || wl.getWeight() <= agg.getBound().ub)){
				continue;
			}
		}

		if (getSolver()->value(wl.getLit()) == l_Undef) {
			found++;
			l = wl.getLit();
			w = wl.getWeight();
		} else if (getSolver()->value(wl.getLit()) == l_True) {
			found=2; //hack to stop immediately, because no propagation necessary
		}
	}
	if (found==1) {
		//basedon is not really relevant for max
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, BASEDONBOTH, l, w));
	}
	return confl;
}

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
rClause SPFWAgg::propagate(const Agg& agg, bool headtrue) {
	rClause c = nullPtrClause;
	//if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
	//	return nullPtrClause;
	//}

	TypedSet& set = getSet();
	const vwl& wls = set.getWL();
	vwl::const_iterator from = wls.end();
	Weight weightbound;

	//FIXME solve for double bounds
	bool ub = agg.hasUB();
	const Weight& bound = ub?agg.getBound().ub:agg.getBound().lb;
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

#ifdef INTWEIGHT
	if(weightbound == INT_MAX || weightbound == INT_MIN) {
		return c;
	}
#endif

	from = lower_bound(wls.begin(), wls.end(), weightbound);
	if (from == getSet().getWL().end()) {
		return c;
	}

	for (vwl::const_iterator u = from; c == nullPtrClause && u < wls.end(); u++) {
		const Lit& l = (*u).getLit();
		//TODO precondition?
		bool propagate = getSolver()->value(l)==l_Undef;
		if(!propagate && getSolver()->getPCSolver()->getLevel(var(l))==getSolver()->getPCSolver()->getCurrentDecisionLevel()){
			bool found = false;
			for(vprop::const_iterator i=getTrail().back().props.begin(); !found && i<getTrail().back().props.end(); i++){
				if(var(l)==var((*i).getLit())){
					found = true;
				}
			}
			propagate = !found;
		}
		//Only propagate those that are not already known in the aggregate solver!
		if (propagate) {
			if ((agg.hasUB() && headtrue) || (!agg.hasUB() && !headtrue)) {
				c = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, ~l, (*u).getWeight()));
			} else {
				c = getSet().getSolver()->notifySolver(new AggReason(agg, basedon, l, (*u).getWeight()));
			}
		}
	}
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

#ifdef INTWEIGHT
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
			AggBound b = (*i)->getBound();
			b.ub = getSet().getType().add(b.ub, totalneg);
			b.lb = getSet().getType().add(b.lb, totalneg);
			(*i)->setBound(b);
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
#ifdef INTWEIGHT
	//Test whether the total product of the weights is not infinity for intweights
	Weight total(1);
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); i++) {
		if(INT_MAX/total < (*i).getWeight()) {
			throw idpexception("The total product of weights exceeds max-int, correctness cannot be guaranteed in limited precision.\n");
		}
		total *= (*i).getWeight();
	}
#endif

	FWAgg::initialize(unsat, sat);
}
