/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/AggSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "satsolver/SATSolver.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "utils/Print.hpp"

#include <assert.h>

using namespace std;
#ifndef __GXX_EXPERIMENTAL_CXX0X__
using namespace std::tr1;
#endif
using namespace MinisatID;

Weight	Agg::getCertainBound() const {
	return bound.bound-getSet()->getKnownBound();
}

paggprop AggProp::max = paggprop (new MaxProp());
//paggprop AggProp::min = paggprop (new MinProp());
paggprop AggProp::sum = paggprop (new SumProp());
paggprop AggProp::card = paggprop (new CardProp());
paggprop AggProp::prod = paggprop (new ProdProp());

bool SumProp::isMonotone(const Agg& agg, const Weight& w) const {
	return (agg.hasUB() && w < 0) || (!agg.hasUB() && w > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const Weight& w) const {
	assert(w == 0 || w >= 1);
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

Weight SumProp::getMinPossible(const TypedSet& set) const{
	Weight min = getESV();
	for (vwl::const_iterator j = set.getWL().begin(); j < set.getWL().end(); ++j) {
		if((*j).getWeight() < 0){
			min = this->add(min, (*j).getWeight());
		}
	}
	return min;
}

Weight SumProp::getMaxPossible(const TypedSet& set) const {
	Weight max = getESV();
	for (vwl::const_iterator j = set.getWL().begin(); j < set.getWL().end(); ++j) {
		if((*j).getWeight() > 0){
			max = this->add(max, (*j).getWeight());
		}
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

// MAX Prop

bool MaxProp::isMonotone(const Agg& agg, const Weight& w) const {
	const Weight& w2 = agg.getCertainBound();
	return (agg.hasUB() && w2 <= w) || (!agg.hasUB());
}

Weight MaxProp::getMinPossible(const TypedSet&) const{
	return getESV();
}

Weight MaxProp::getMaxPossible(const TypedSet& set) const {
	Weight max = getESV();
	for(vwl::const_iterator j = set.getWL().begin(); j<set.getWL().end(); ++j){
		max = this->add(max, (*j).getWeight());
	}
	return max;
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

//// MIN Prop
//
//bool MinProp::isMonotone(const Agg& agg, const Weight& w) const {
//	const Weight& w2 = agg.getCertainBound();
//	return (agg.hasLB() && w <= w2) || (!agg.hasLB());
//}
//
//Weight MinProp::getMinPossible(const TypedSet& set) const{
//	Weight min = getESV();
//	for(vwl::const_iterator j = set.getWL().begin(); j<set.getWL().end(); ++j){
//		min = this->add(min, (*j).getWeight());
//	}
//	return min;
//}
//
//Weight MinProp::getMaxPossible(const TypedSet&) const {
//	return getESV();
//}
//
//Weight MinProp::getCombinedWeight(const Weight& first, const Weight& second) const {
//	return first < second ? first : second;
//}
//
//WL MinProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const {
//	if (one.getWeight() < two.getWeight()) {
//		if (set->getKnownBound() > two.getWeight()) {
//			set->setKnownBound(two.getWeight());
//		}
//		return one;
//	} else {
//		if (set->getKnownBound() > one.getWeight()) {
//			set->setKnownBound(one.getWeight());
//		}
//		return two;
//	}
//}

// PROD Prop

//INVARIANT: only positive weights in prodagg
Weight ProdProp::getMinPossible(const TypedSet&) const{
	return getESV();
}

Weight ProdProp::getMaxPossible(const TypedSet& set) const {
	Weight max = getESV();
	for(vwl::const_iterator j = set.getWL().begin(); j<set.getWL().end(); ++j){
		if((*j).getWeight() > 0){
			max = this->add(max, (*j).getWeight());
		}
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
	assert(rhs!=0); //FIXME should prevent this from happening
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
	//ofwel aggregaten voor doubles ondersteunen (hPropagatoret eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	NoSupportForBothSignInProductAgg(cerr, one.getLit(), two.getLit());
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

//AGGREGATES

bool MinisatID::isSatisfied(const Agg& agg, const Weight& min, const Weight& max){
	if(agg.hasUB()){
		return max<=agg.getCertainBound();
	}else{ //LB
		return min>=agg.getCertainBound();
	}
}

bool MinisatID::isSatisfied(const Agg& agg, const minmaxBounds& bounds){
	if(agg.hasUB()){
		return bounds.max<=agg.getCertainBound();
	}else{ //LB
		return bounds.min>=agg.getCertainBound();
	}
}

bool MinisatID::isFalsified(const Agg& agg, const Weight& min, const Weight& max){
	if(agg.hasUB()){
		return min>agg.getCertainBound();
	}else{ //LB
		return max<agg.getCertainBound();
	}
}

bool MinisatID::isFalsified(const Agg& agg, const minmaxBounds& bounds){
	if(agg.hasUB()){
		return bounds.min>agg.getCertainBound();
	}else{ //LB
		return bounds.max<agg.getCertainBound();
	}
}

/**
 * IMPORTANT: not usable for types without remove!
 * if addtoset: weight should be considered as the weight of a literal being added to the set (from unknown)
 * 		if weight is pos: min will increase, so add to min
 * 		if weight is neg: max will decrease, so add to max
 * if !addtoset: consider weight as weight of the literal being removed from the set (from unknown)
 * 		if weight is pos: max will decrease, so remove from max
 * 		if weight is neg: min will increase, so remove from min
 */
void MinisatID::addValue(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds){
	addValue(type, weight, addtoset, bounds.min, bounds.max);
}
void MinisatID::addValue(const AggProp& type, const Weight& weight, bool addtoset, Weight& min, Weight& max){
	bool pos = weight>=0;
	if(pos && addtoset){
		min = type.add(min, weight);
	}else if(pos && !addtoset){
		max = type.remove(max, weight);
	}else if(!pos && addtoset){
		max = type.add(max, weight);
	}else{ //!pos && !addtoset
		min = type.remove(min, weight);
	}
}

void MinisatID::removeValue(const AggProp& type, const Weight& weight, bool wasinset, minmaxBounds& bounds) {
	removeValue(type, weight, wasinset, bounds.min, bounds.max);
}

void MinisatID::removeValue(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max) {
	bool pos = weight>=0;
	if(pos && wasinset){
		min = type.remove(min, weight);
	}else if(pos && !wasinset){
		max = type.add(max, weight);
	}else if(!pos && wasinset){
		max = type.remove(max, weight);
	}else{ //!pos && !wasinset
		min = type.add(min, weight);
	}
}

// TypedSet

bool printedwarning = false;

AggPropagator*	MaxProp::createPropagator(TypedSet* set) const{
	if(set->isUsingWatches() && !printedwarning){
		clog <<">> Currently max/min aggregates never use watched-literal-schemes.\n";
		printedwarning = true;
	}
	return new MaxFWAgg(set);
}

/*Propagator*	MinProp::createPropagator(TypedSet* set) const{
	if(set->isUsingWatches() && !printedwarning){
		clog <<">> Currently max/min aggregates never use watched-literal-schemes.\n";
		printedwarning = true;
	}
	return new MinFWAgg(set);
}*/

AggPropagator*	SumProp::createPropagator(TypedSet* set) const{
	set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if(set->isUsingWatches()){
		return new GenPWAgg(set);
	}else{
		return new SumFWAgg(set);
	}
}

AggPropagator*	ProdProp::createPropagator(TypedSet* set) const{
	set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if(set->isUsingWatches()){
		return new GenPWAgg(set);
	}else{
		return new ProdFWAgg(set);
	}
}

void TypedSet::addAgg(Agg* aggr){
	assert(aggr!=NULL);
	aggregates.push_back(aggr);
	aggr->setTypedSet(this);
	aggr->setIndex(aggregates.size()-1);
}

void TypedSet::replaceAgg(const agglist& repl){
	for(agglist::const_iterator i=aggregates.begin(); i<aggregates.end(); ++i){
		assert((*i)->getSet()==this);
		(*i)->setTypedSet(NULL);
		(*i)->setIndex(-1);
	}
	aggregates.clear();
	for(agglist::const_iterator i=repl.begin(); i<repl.end(); ++i){
		addAgg(*i);
	}
}

void TypedSet::replaceAgg(const agglist& repl, const agglist& del){
	replaceAgg(repl);
	for(agglist::const_iterator i=del.begin(); i<del.end(); ++i){
		delete *i;
	}
}

/*
 * Initialize the datastructures. If it's neither sat nor unsat and it is defined, notify the pcsolver of this
 */
void TypedSet::initialize(bool& unsat, bool& sat, vps& sets) {
	for(vector<AggTransformation*>::iterator i=transformations.begin(); !sat && !unsat && i<transformations.end(); ++i) {
		AggTransformation* transfo = *i;
		transformations.erase(i); i--;
		transfo->transform(getSolver(), this, sets, unsat, sat);
	}

	if(sat || unsat){ return; }

	setProp(getType().createPropagator(this));
	prop->initialize(unsat, sat);

	if(sat || unsat){ return; }

	for (agglist::const_iterator i = getAgg().begin(); i < getAgg().end(); ++i) {
		if ((*i)->isDefined()) {
			getSolver()->notifyDefinedHead(var((*i)->getHead()), (*i)->getDefID());
		}
	}
}

void TypedSet::addExplanation(AggReason& ar) const {
	vec<Lit> lits;
	lits.push(ar.getPropLit());
	getProp()->getExplanation(lits, ar);
	ar.setClause(lits);

	if(getSolver()->verbosity()>=3){
		clog <<"Explanation for deriving " <<ar.getPropLit();
		clog <<" in expression ";
		print(getSolver()->verbosity(), ar.getAgg(), false);
		clog <<" is ";
		for(int i=0; i<lits.size(); ++i){
			clog <<" " <<lits[i];
		}
		clog <<"\n";
	}
}

AggPropagator::AggPropagator(TypedSet* set)
		:set(set), aggsolver(set->getSolver()), satsolver(set->getSolver()->getSATSolver()){

}

// Final initialization call!
void AggPropagator::initialize(bool& unsat, bool& sat) {
	for (agglist::const_iterator i = getSet().getAgg().begin(); i < getSet().getAgg().end(); ++i) {
		if((*i)->getSem()==IMPLICATION){
			getSolver()->setHeadWatch(~(*i)->getHead(), (*i));
		}else{
			getSolver()->setHeadWatch((*i)->getHead(), (*i));
			getSolver()->setHeadWatch(~(*i)->getHead(), (*i));
		}
	}
}

// Maximize speed of requesting values! //FIXME add to other solvers
lbool AggPropagator::value(const Lit& l) const {
	return satsolver->value(l);
}

Weight AggPropagator::getValue() const {
	Weight total = getSet().getType().getESV();
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); ++i){
		lbool val = value((*i).getLit());
		assert(val!=l_Undef);

		if(val==l_True){
			total = getSet().getType().add(total, (*i).getWeight());
		}
	}
	return total;
}

// RECURSIVE AGGREGATES

bool MaxProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	bool justified = true;
	const vwl& wl = set->getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() > agg.getCertainBound(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit()); //push negative literal, because it should become false
			} else if (real || currentjust.getElem(var((*i).getLit())) != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	}

	if(justified && agg.hasLB()){
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && (*i).getWeight() >= agg.getCertainBound(); ++i) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				justified = true;
			} else if (real || currentjust.getElem(var((*i).getLit())) != 0) {
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
bool SPProp::canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	TypedSet* set = agg.getSet();
	const AggProp& type = agg.getSet()->getType();
	bool justified = true;
	const vwl& wl = set->getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		Weight bestpossible = type.getMaxPossible(*set);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push(~(*i).getLit());
				bestpossible = type.remove(bestpossible, (*i).getWeight());
				if (bestpossible <= agg.getCertainBound()) {
					justified = true;
				}
			} else if (real || currentjust.getElem(var((*i).getLit())) != 0) {
				nonjstf.push(var((*i).getLit()));
			}
		}
	}
	if(justified && agg.hasLB()){
		justified = false;
		Weight bestcertain = set->getType().getMinPossible(*set);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(*i, currentjust, real, set->getSolver())) {
				jstf.push((*i).getLit());
				bestcertain = type.add(bestcertain, (*i).getWeight());
				if (bestcertain >= agg.getCertainBound()) {
					justified = true;
				}
			} else if (real || currentjust.getElem(var((*i).getLit())) != 0) {
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
 for(int i=0; i<jstf.size(); ++i){
 print(jstf[i]); reportf(" ");
 }
 reportf("\n");
 }else{
 reportf("no justification found.\n");
 }
 }

 return justified;
 }*/
