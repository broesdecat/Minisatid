/*
 * FullyWatched.cpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#include "solvers/modules/aggsolver/FullyWatched.hpp"

#include "solvers/modules/AggSolver.hpp"
#include "solvers/theorysolvers/PCSolver.hpp"

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
	Propagator(set), currentbestcertain(0), currentbestpossible(0) {

}

void FWAgg::initialize(bool& unsat, bool& sat) {
	if (getSet().getAgg().size() == 0) {
		sat = true;
		return;
	}
	//TODO set reduction was here!
	truth.resize(getSet().getWL().size(), l_Undef);

	setCP(getSet().getBestPossible());
	setCC(getSet().getESV());

	int startsize = getSet().getAgg().size();
	headvalue.resize(startsize, l_Undef);
	headindex.resize(startsize, -1);
	nomoreprops.resize(startsize, false);
	optimagg.resize(startsize, false);
	headproptime.resize(startsize, -1);

	int i = 0, j = 0;
	for (; !unsat && i < getSet().getAgg().size(); i++) {
		pagg agg = getSet().getAgg()[i];
		lbool result = initialize(*agg);
		if (result == l_True && !agg->isDefined()) {
			//If after initialization, the head will have a fixed value, then this is
			//independent of any further propagations within that aggregate.
			//BUT ONLY if it is not defined (or at a later stage, if it cannot be in any loop)
			getSet().getSolver()->removeHeadWatch(var(agg->getHead()));
			delete agg;
		} else if (result == l_False) {
			unsat = true; //UNSAT because always false
			return;
		} else {
			agg->setIndex(j);
			getSet().getAgg()[j++] = agg;
		}
	}
	getSet().getAgg().resize(j);
	headvalue.resize(j, l_Undef);
	headindex.resize(j, -1);
	nomoreprops.resize(j, false);
	optimagg.resize(j, false);
	headproptime.clear(); //if it has been propagated before, it has been dropped
	headproptime.resize(j, -1);

	for (int j = 0; j < getSet().getWL().size(); j++) {
		const Lit& l = getSet().getWL()[j].getLit();
		Var v = var(l);
		getSet().getSolver()->addPermWatch(v, new Watch(getSetp(), j, true, sign(l) ? false : true));
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

	lbool hv = canPropagateHead(agg, getCC(), getCP());
	bool alwaystrue = false;
	if (hv != l_Undef && !optimagg[agg.getIndex()]) {
		alwaystrue = true;
		//reportf("No more propagations for %d", gprintVar(var(head)));
	}
	if (hv == l_True) {
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, mkLit(-1), CPANDCC, agg.getHead(), true));
	} else if (hv == l_False) {
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, mkLit(-1), CPANDCC, ~agg.getHead(), true));
	}
	if (confl != nullPtrClause) {
		return l_False;
	}

	return alwaystrue ? l_True : l_Undef;
}

/*void FWAgg::backtrack(const Agg& agg, int stacksize) {
	if (headproptime[agg.getIndex()]!=-1 && headproptime[agg.getIndex()] > stacksize) {
		headproptime[agg.getIndex()] = -1;
	}
}

void FWAgg::backtrack(const Agg& agg) {
	if (nomoreprops[agg.getIndex()]) {
		return;
	}

	headvalue[agg.getIndex()] = l_Undef;
	headindex[agg.getIndex()] = -1;
}*/

//FIXME PROBABLY INCORRECT
void FWAgg::backtrack(int nblevels, int untillevel){
/*	if (getStack().size() == 0 || var(getStack().back().getLit()) != var(getSet().getWL()[w.getIndex()].getLit())) {
		return; //Only backtrack if it was effectively propagated
	}
	const PropagationInfo& pi = stack.back();
	stack.pop_back();

	assert(pi.getType() != HEAD && var(pi.getLit()) == var(getSet().getWL()[w.getIndex()].getLit()));

	truth[w.getIndex()] = l_Undef;
	setCC(pi.getPC());
	setCP(pi.getPP());

	int s = stack.size();
	for (vpagg::const_iterator i = getSet().getAgg().begin(); i < getSet().getAgg().end(); i++) {
		backtrack(**i, s);
	}*/
}

/**
 * Returns non-owning pointer
 */
rClause FWAgg::propagate(const Agg& agg) {
	if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
		return nullPtrClause;
	}

	lbool headtrue = getSet().getSolver()->value(agg.getHead());
	headvalue[agg.getIndex()] = headtrue;
	headindex[agg.getIndex()] = getStack().size();
	rClause confl = propagate(agg, headtrue == l_True);
	return confl;
}

rClause FWAgg::propagate(const Lit& p, pw ws) {
	Occurrence tp;
	if (ws->getType() == POS) {
		tp = sign(p) ? NEG : POS;
	} else {
		tp = sign(p) ? POS : NEG;
	}

	const WL& wl = getSet().getWL()[ws->getIndex()];
	stack.push_back(PropagationInfo(p, wl.getWeight(), tp));
	truth[ws->getIndex()] = tp == POS ? l_True : l_False;
	tp == POS ? addToCertainSet(wl) : removeFromPossibleSet(wl);

	rClause confl = nullPtrClause;
	for (int i = 0; i < getSet().getAgg().size() && confl == nullPtrClause; i++) {
		const Agg& pa = *getSet().getAgg()[i];

		if (getSet().getSolver()->verbosity() >= 6) {
			report("Propagating into aggr: ");
			Aggrs::printAgg(pa, true);
		}

		lbool hv = headvalue[pa.getIndex()];
		if (hv != l_Undef) { //head is already known
			assert(canPropagateHead(pa, getCC(), getCP()) != (hv == l_True ? l_False : l_True)); //A conflicting propagation is not possible if we have complete propagation
			confl = propagate(pa, hv == l_True);
		} else { //head is not yet known, so at most the head can be propagated
			lbool result = canPropagateHead(pa, getCC(), getCP());
			if (result != l_Undef) {
				rClause	cc = getSet().getSolver()->notifySolver(new AggReason(pa, p, CPANDCC, result == l_True ? pa.getHead() : ~pa.getHead(), true));
				confl = cc;
			}
		}
	}
	return confl;
}

lbool FWAgg::canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const {
	if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
		return headvalue[agg.getIndex()];
	}

	if ((agg.isLower() && CC > agg.getBound()) || (agg.isUpper() && CP < agg.getBound())) {
		headproptime[agg.getIndex()] = getStack().size();
		return l_False;
	} else if ((agg.isLower() && CP <= agg.getBound()) || (agg.isUpper() && CC>= agg.getBound())) {
		headproptime[agg.getIndex()] = getStack().size();
		return l_True;
	} else {
		return l_Undef;
	}
}

/**
 * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
 * which is equivalent with the clause bigvee{~l|l in L+} or p
 * and this is returned as the set {~l|l in L+}
 */
void FWAgg::getExplanation(vec<Lit>& lits, const AggReason& ar) {
	//assert(ar.getAgg() == agg);
	//assert(agg->getSet()==this);

	int index = -1;
	bool includereason = false;
	if(toInt(ar.getLit())!=-1){
		for (int i = 0; i < getStack().size(); i++) {
			if (getStack()[i].getLit() == ar.getLit()) {
				includereason = true; //To also include the literal which caused propagation
				index = i;
				break;
			}
			if(getStack()[i].getLit() == ar.getPropLit()){
				index = i;
				break;
			}
		}
		if (index==-1) {
			index = getStack().size();
		}
	}

	const Agg& agg = ar.getAgg();
	const Lit& head = agg.getHead();

	if (!ar.isHeadReason() && index >= headindex[agg.getIndex()]) {
		//the head literal is saved as it occurred in the theory, so adapt for its current truth value!
		lits.push(getSet().getSolver()->isTrue(head) ? ~head : head);
	}

	// Allows for better minimization of explanation: the last literal was certainly part of the explanation, but maybe not the ones before
	if(includereason){
		lits.push(~ar.getLit());
	}

	//assert(ar.isHeadReason() || getPCSolver()->getLevel(ar.getLit())<=s->getStackSize());

	//	This is correct, but not minimal enough. We expect to be able to do better
	//	for(lprop::const_iterator i=s->getStackBegin(); counter<ar.getIndex() && i<s->getStackEnd(); i++,counter++){
	//		lits.push(~(*i).getLit());
	//	}

	int counter = 0;
	if (ar.getExpl() != HEADONLY) {
		for (vprop::const_iterator i = getStack().begin(); counter < index && i < getStack().end(); i++, counter++) {
			//for(lprop::const_iterator i=s->getStackBegin(); var(ar.getLit())!=var((*i).getLit()) && i<s->getStackEnd(); i++){
			switch (ar.getExpl()) {
			case BASEDONCC:
				if ((*i).getType() == POS) {
					lits.push(~(*i).getLit());
				}
				break;
			case BASEDONCP:
				if ((*i).getType() == NEG) {
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

	if (getSet().getSolver()->verbosity() >= 5) {
//		reportf("STACK: ");
//		for (vprop::const_iterator i = getStack().begin(); i < getStack().end(); i++) {
//			gprintLit((*i).getLit());
//			reportf(" ");
//		}
//		reportf("\n");

		report("Aggregate explanation for ");
		gprintLit(ar.getPropLit());

		report(" is");
		for (int i = 0; i < lits.size(); i++) {
			report(" ");
			gprintLit(lits[i]);
		}
		report("\n");
	}
}

/*****************
 * MAX AGGREGATE *
 *****************/

MaxFWAgg::MaxFWAgg(TypedSet* set) :
	FWAgg(set) {
}

void MaxFWAgg::initialize(bool& unsat, bool& sat) {
	if (getSet().getAgg().size() == 1) { //Simple heuristic to choose for encoding as SAT
		//SAT encoding, not used yet
		bool notunsat = true;
		for (int i = 0; notunsat && i < getSet().getAgg().size(); i++) {
			/*
			 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
			 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
			 */
			vec<Lit> clause;
			const pagg agg = getSet().getAgg()[i];
			if (agg->isDefined()) {
				for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); i < getSet().getWL().rend()
							&& (*i).getWeight() >= agg->getBound(); i++) {
					if (agg->isLower() && (*i).getWeight() == agg->getBound()) {
						break;
					}
					if (agg->isLower()) {
						clause.push(~(*i).getLit());
					} else {
						clause.push((*i).getLit());
					}
				}
				notunsat = getSet().getSolver()->getPCSolver()->addRule(agg->isLower() ? LB : UB,agg->getHead(),clause);
			} else {
				clause.push(agg->isLower() ? agg->getHead() : ~agg->getHead());
				for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); i < getSet().getWL().rend()
							&& (*i).getWeight() >= agg->getBound(); i++) {
					if (agg->isLower() && (*i).getWeight() == agg->getBound()) {
						break;
					}
					clause.push((*i).getLit());
				}
				notunsat = getSet().getSolver()->getPCSolver()->addClause(clause);
				for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); notunsat && i < getSet().getWL().rend()
							&& (*i).getWeight() >= agg->getBound(); i++) {
					if (agg->getBound() && (*i).getWeight() == agg->getBound()) {
						break;
					}
					clause.clear();
					clause.push(agg->isLower() ? ~agg->getHead() : agg->getHead());
					clause.push(~(*i).getLit());
					notunsat = getSet().getSolver()->getPCSolver()->addClause(clause);
				}
			}
		}
		unsat = !notunsat;
		sat = true;
		return;
	} else {
		FWAgg::initialize(unsat, sat);
	}
}

void MaxFWAgg::addToCertainSet(const WL& l) {
	if (l.getWeight() > getCC()) {
		setCC(l.getWeight());
	}
}

void MaxFWAgg::removeFromPossibleSet(const WL& l) {
	if (l.getWeight() == getCP()) {
		bool found = false;
		for (int i = 0; i < getSet().getWL().size(); i++) {
			if (truth[i] != l_False) {
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
	if(nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1){ return nullPtrClause; }

	if (false) { //ULTIMATE propagation
		//return maxultimatepropagation(agg, headtrue);
		return NULL;
	} else {
		rClause confl = nullPtrClause;
		if (headtrue && agg.isLower()) {
			for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
						< getSet().getWL().rend() && agg.getBound() < (*i).getWeight(); i++) {
				//because these propagations are independent of the other set literals, they can also be written as clauses
				confl = getSet().getSolver()->notifySolver(new AggReason(agg, agg.getHead(), HEADONLY, ~(*i).getLit()));
			}
		} else if (!headtrue && agg.isUpper()) {
			for (vwl::const_reverse_iterator i = getSet().getWL().rbegin(); confl == nullPtrClause && i
						< getSet().getWL().rend() && agg.getBound() <= (*i).getWeight(); i++) {
				confl = getSet().getSolver()->notifySolver(new AggReason(agg, ~agg.getHead(), HEADONLY, ~(*i).getLit()));
			}
		}
		if (confl == nullPtrClause) {
			confl = propagateAll(agg, headtrue);
		}
		return confl;
	}
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

	if(nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1){ return confl; }

	if ((agg.isLower() && headtrue) || (agg.isUpper() && !headtrue)) {
		return confl;
	}

	int pos = -1;
	bool exactlyoneleft = true;
	for (int i = 0; exactlyoneleft && i < getSet().getWL().size(); i++) {
		const WL& wl = getSet().getWL()[i];
		if ((agg.isUpper() && headtrue && wl.getWeight() >= agg.getBound()) || (agg.isLower()
					&& !headtrue && wl.getWeight() > agg.getBound())) {
			if (truth[i] == l_Undef) {
				if (pos != -1) {
					exactlyoneleft = false;
				} else {
					pos = i;
				}
			} else if (truth[i] == l_True) {
				exactlyoneleft = false;
			}
		}
	}
	if (exactlyoneleft) {
		//TODO BASEDONCP is not correct enough (ONCPABOVEBOUND)
		confl = getSet().getSolver()->notifySolver(new AggReason(agg, headtrue?agg.getHead():~agg.getHead(), BASEDONCP, getSet().getWL()[pos].getLit()));
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

rClause SPFWAgg::propagate(const Agg& agg, bool headtrue) {
	if (nomoreprops[agg.getIndex()] || headproptime[agg.getIndex()]!=-1) {
		return nullPtrClause;
	}

	rClause c = nullPtrClause;
	Weight weightbound(0);

	Expl basedon = CPANDCC;
	//determine the lower bound of which weight literals to consider
	if (headtrue) {
		if (agg.isLower()) {
			basedon = BASEDONCC;
			weightbound = getSet().getType().remove(agg.getBound(), getCC());
			//+1 because larger and not eq
			if (getSet().getType().add(weightbound, getCC()) == agg.getBound()) {
				weightbound += 1;
			}
		} else {
			basedon = BASEDONCP;
			weightbound = getSet().getType().remove(getCP(), agg.getBound());
			//+1 because larger and not eq
			if (getSet().getType().add(weightbound, agg.getBound()) == getCP()) {
				weightbound += 1;
			}
		}
	} else {
		if (agg.isLower()) {
			basedon = BASEDONCP;
			weightbound = getSet().getType().remove(getCP(), agg.getBound());
		} else {
			basedon = BASEDONCC;
			weightbound = getSet().getType().remove(agg.getBound(), getCC());
		}
	}

#ifdef INTWEIGHT
	if(weightbound == INT_MAX || weightbound == INT_MIN) {
		return c;
	}
#endif

	vwl::const_iterator pos = lower_bound(getSet().getWL().begin(), getSet().getWL().end(), weightbound);
	if (pos == getSet().getWL().end()) {
		return c;
	}

	//find the index of the literal
	int start = 0;
	vwl::const_iterator it = getSet().getWL().begin();
	while (it != pos) {
		it++;
		start++;
	}

	for (int u = start; c == nullPtrClause && u < getSet().getWL().size(); u++) {
		if (truth[u] == l_Undef) {//if already propagated as an aggregate, then those best-values have already been adapted
			const Lit& l = getSet().getWL()[u].getLit();
			if ((agg.isLower() && headtrue) || (agg.isUpper() && !headtrue)) {
				c = getSet().getSolver()->notifySolver(new AggReason(agg, headtrue?agg.getHead():~agg.getHead(), basedon, ~l));
			} else {
				c = getSet().getSolver()->notifySolver(new AggReason(agg, headtrue?agg.getHead():~agg.getHead(), basedon, l));
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
			addToBounds(**i, totalneg);
		}
	}

	FWAgg::initialize(unsat, sat);
}

void SumFWAgg::getMinimExplan(const Agg& agg, vec<Lit>& lits) {
	Weight certainsum = getSet().getESV();
	Weight possiblesum = getSet().getBestPossible();

	bool explained = false;
	if ((agg.isLower() && certainsum > agg.getBound()) || (agg.isUpper() && certainsum
				>= agg.getBound()) || (agg.isLower() && possiblesum <= agg.getBound())
				|| (agg.isUpper() && possiblesum < agg.getBound())) {
		explained = true;
	}

	for (vprop::const_iterator i = getStack().begin(); !explained && i < getStack().end(); i++) {
		bool push = false;
		if ((*i).getType() == POS) { //means that the literal in the set became true
			certainsum += (*i).getWeight();

			if (agg.isLower()) {
				push = true;
				if (agg.getBound() < certainsum) {
					explained = true;
				}
			}
		} else if ((*i).getType() == NEG) { //the literal in the set became false
			possiblesum -= (*i).getWeight();

			if (agg.isUpper()) {
				push = true;
				if (possiblesum < agg.getBound()) {
					explained = true;
				}
			}
		}
		if (push) {
			lits.push(~(*i).getLit());
		}
	}

	assert(explained);
}
void SumFWAgg::addToBounds(Agg& agg, const Weight& w) {
	if (agg.isLower()) {
		agg.setBound(getSet().getType().add(agg.getBound(), w));
	} else {
		agg.setBound(getSet().getType().add(agg.getBound(), w));
	}
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
