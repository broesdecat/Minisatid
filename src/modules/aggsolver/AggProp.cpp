#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/AggSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "PbSolver.h"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include <assert.h>

using namespace std;
using namespace tr1;
using namespace MinisatID;
using namespace Aggrs;

const Weight	Agg::getCertainBound() const {
	return bound.bound-getSet()->getKnownBound();
}

shared_ptr<AggProp> AggProp::max = shared_ptr<AggProp> (new MaxProp());
shared_ptr<AggProp> AggProp::sum = shared_ptr<AggProp> (new SumProp());
shared_ptr<AggProp> AggProp::card = shared_ptr<AggProp> (new CardProp());
shared_ptr<AggProp> AggProp::prod = shared_ptr<AggProp> (new ProdProp());

bool MaxProp::isMonotone(const Agg& agg, const WL& l) const {
	const Weight& w = agg.getCertainBound();
	return (agg.hasUB() && l.getWeight() <= w) || (!agg.hasUB());
}

bool SumProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.hasUB() && l.getWeight() < 0) || (!agg.hasUB() && l.getWeight() > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const WL& l) const {
	assert(l.getWeight() == 0 || l.getWeight() >= 1);
	return !agg.hasUB();
}

Weight SumProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef NOARBITPREC
	if (lhs > 0 && rhs > 0 && posInfinity() - lhs < rhs) {
		return posInfinity();
	} else if (lhs < 0 && rhs < 0 && negInfinity() - lhs > rhs) {
		return negInfinity();
	}
#endif
	return lhs + rhs;
}

Weight SumProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight SumProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getType().getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight SumProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() < two.getWeight()) {
		set->setKnownBound(set->getKnownBound() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setKnownBound(set->getKnownBound() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// MAX Prop
///////

Weight MaxProp::getBestPossible(TypedSet* set) const {
	return set->getWL().back().getWeight();
}

Weight MaxProp::getCombinedWeight(const Weight& first, const Weight& second) const {
	return first > second ? first : second;
}

WL MaxProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	if (one.getWeight() > two.getWeight()) {
		if (set->getKnownBound() < two.getWeight()) {
			set->setKnownBound(two.getWeight());
		}
		return one;
	} else {
		if (set->getKnownBound() < one.getWeight()) {
			set->setKnownBound(one.getWeight());
		}
		return two;
	}
}

///////
// PROD Prop
///////

Weight ProdProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getType().getESV();
	for(vwl::const_iterator j = set->getWL().begin(); j<set->getWL().end(); j++){
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight ProdProp::add(const Weight& lhs, const Weight& rhs) const {
	assert(lhs!=0 && rhs!=0);
#ifdef NOARBITPREC
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0){
		l = -l;
		sign = true;
	}
	if(r<0){
		r = -r;
		sign = !sign;
	}
	if(posInfinity()/l < r){
		return sign ? negInfinity() : posInfinity();
	}
#endif
	return lhs * rhs;
}

Weight ProdProp::remove(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	if (rhs != 0) {
		w = lhs / rhs;
		if (w == 1 && lhs > rhs) {
			w = 2;
		}
	}

	return w;
}

Weight ProdProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL ProdProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (het eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	report("Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ");
	gprintLit(one.getLit());
	report("or ");
	gprintLit(two.getLit());
	report("by a tseitin.\n");
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

///////
// TypedSet
///////

Propagator*	MaxProp::createPropagator(TypedSet* set, bool pw) const{
	return new MaxFWAgg(set);
}

Propagator*	SumProp::createPropagator(TypedSet* set, bool pw) const{
	if(pw){
		if(getType()==CARD){
			return new CardGenPWAgg(set);
		}else{
			return new SumGenPWAgg(set);
		}
	}
	//if(pw && getType()==CARD){
		//FIXME: CURRENTLY WORKS INCORRECTLY:
		//one issue with propagated value instead of value
		//one issue with multiple watches becoming false
		//...
		//recommendation: scrap
		//return new CardPWAgg(set);
	//}
	return new SumFWAgg(set);
}

Propagator*	ProdProp::createPropagator(TypedSet* set, bool pw) const{
	if(pw){
		return new GenPWAgg(set);
	}
	return new ProdFWAgg(set);
}

void TypedSet::addAgg(Agg* aggr){
	assert(aggr!=NULL);
	aggregates.push_back(aggr);
	aggr->setTypedSet(this);
	aggr->setIndex(aggregates.size()-1);
}

void TypedSet::replaceAgg(const vpagg& repl){
	for(vpagg::const_iterator i=aggregates.begin(); i<aggregates.end(); i++){
		(*i)->setTypedSet(NULL);
		(*i)->setIndex(-1);
	}
	aggregates.clear();
	for(vector<Agg*>::const_iterator i=repl.begin(); i<repl.end(); i++){
		addAgg(*i);
	}
}

/*
 * Initialize the datastructures. If it's neither sat nor unsat and it is defined, notify the pcsolver of this
 */
void TypedSet::initialize(bool& unsat, bool& sat) {
	setProp(getType().createPropagator(this, this->getSolver()->getPCSolver()->modes().watchedagg));
	prop->initialize(unsat, sat);

	if (!sat && !unsat) {
		for (vsize i = 0; i < getAgg().size(); i++) {
			if (getAgg()[i]->isDefined()) {
				getSolver()->notifyDefinedHead(var(getAgg()[i]->getHead()));
			}
		}
	}
}

Propagator::Propagator(TypedSet* set):set(set), aggsolver(set->getSolver()){

}

// Final initialization call!
void Propagator::initialize(bool& unsat, bool& sat) {
	for (vsize i = 0; i < getSet().getAgg().size(); i++) {
		getSolver()->setHeadWatch(var(getSet().getAgg()[i]->getHead()), getSet().getAgg()[i]);
	}
}

lbool Propagator::value(const Lit& l) const {
	return getSolver()->value(l);
}

lbool Propagator::propagatedValue(const Lit& l) const {
	return getSolver()->propagatedValue(l);
}

/************************
 * RECURSIVE AGGREGATES *
 ************************/

bool MaxProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	bool justified = true;
	const vwl& wl = set->getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() > agg.getCertainBound(); i++) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	}

	if(justified && agg.hasLB()){
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() >= agg.getCertainBound(); i++) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				justified = true;
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if (!justified) {
		jstf.clear();
	}

	return justified;
}

/**
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool SPProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	const AggProp& type = agg.getSet()->getType();
	bool justified = true;
	const vwl& wl = set->getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		Weight bestpossible = type.getBestPossible(set);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit());
				bestpossible = type.remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getCertainBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}
	if(justified && agg.hasLB()){
		justified = false;
		Weight bestcertain = set->getType().getESV();
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				bestcertain = type.add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getCertainBound()) {
					justified = true;
				}
			} else if (real || currentjust[var((*i).getLit())] != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}

	if (!justified) {
		jstf.clear();
	}

	return justified;
}

/*bool SPAgg::canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const {
 //OTHER IMPLEMENTATION (probably buggy)
 pSet s = getSet();

 Weight current = 0;
 if(isLower()){
 current = s->getBestPossible();
 }else{
 current = s->getEmptySetValue();
 }

 bool justified = false;
 if(aggValueImpliesHead(current)){
 justified = true;
 }

 for (lwlv::const_iterator i = s->getWLBegin(); !justified && i < s->getWLEnd(); ++i) {
 if(isMonotone(*i) && s->isJustified(*i, currentjust, real)){
 if(isLower()){
 jstf.push(~(*i).getLit());
 current = this->remove(current, (*i).getWeight());
 }else{
 //if(s->isJustified(*i, currentjust, real)){
 jstf.push((*i).getLit());
 current = this->add(current, (*i).getWeight());
 }

 if (aggValueImpliesHead(current)){
 justified = true;
 }
 }else if(real ||currentjust[var((*i).getLit())]!=0){
 nonjstf.push(var((*i).getLit()));
 }
 }

 if (!justified) {
 jstf.clear();
 }

 if(s->getSolver()->getPCSolver()->modes().verbosity >=4){
 reportf("Justification checked for ");
 printAggrExpr(this);

 if(justified){
 reportf("justification found: ");
 for(int i=0; i<jstf.size(); i++){
 gprintLit(jstf[i]); reportf(" ");
 }
 reportf("\n");
 }else{
 reportf("no justification found.\n");
 }
 }

 return justified;
 }*/
