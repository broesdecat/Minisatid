/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include <cassert>

using namespace std;
using namespace MinisatID;

Weight	Agg::getCertainBound() const {
	return bound.bound-getSet()->getKnownBound();
}

paggprop AggProp::max = paggprop (new MaxProp());
//paggprop AggProp::min = paggprop (new MinProp());
paggprop AggProp::sum = paggprop (new SumProp());
paggprop AggProp::card = paggprop (new CardProp());
paggprop AggProp::prod = paggprop (new ProdProp());

Weight AggProp::getMinPossible(const TypedSet& set)	const { return getMinPossible(set.getWL()); }
Weight AggProp::getMaxPossible(const TypedSet& set)	const { return getMaxPossible(set.getWL()); }

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

Weight SumProp::getMinPossible(const std::vector<WL>& wls) const{
	Weight min = getESV();
	for (vwl::const_iterator j = wls.begin(); j < wls.end(); ++j) {
		if((*j).getWeight() < 0){
			min = this->add(min, (*j).getWeight());
		}
	}
	return min;
}

Weight SumProp::getMaxPossible(const std::vector<WL>& wls) const {
	Weight max = getESV();
	for (vwl::const_iterator j = wls.begin(); j < wls.end(); ++j) {
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

Weight MaxProp::getMinPossible(const std::vector<WL>&) const{
	return getESV();
}

Weight MaxProp::getMaxPossible(const std::vector<WL>& wls) const {
	Weight max = getESV();
	for(vwl::const_iterator j = wls.begin(); j<wls.end(); ++j){
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
Weight ProdProp::getMinPossible(const std::vector<WL>&) const{
	return getESV();
}

Weight ProdProp::getMaxPossible(const std::vector<WL>& wls) const {
	Weight max = getESV();
	for(vwl::const_iterator j = wls.begin(); j<wls.end(); ++j){
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
	//ofwel aggregaten voor doubles ondersteunen (hAggPropagatoret eerste is eigenlijk de beste oplossing)
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

/*AggPropagator*	MinProp::createPropagator(TypedSet* set) const{
	if(set->isUsingWatches() && !printedwarning){
		clog <<">> Currently max/min aggregates never use watched-literal-schemes.\n";
		printedwarning = true;
	}
	return new MinFWAgg(set);
}*/

AggPropagator*	SumProp::createPropagator(TypedSet* set) const{
	//FIXME aggheur set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if(set->isUsingWatches()){
		return new GenPWAgg(set);
	}else{
		return new SumFWAgg(set);
	}
}

AggPropagator*	ProdProp::createPropagator(TypedSet* set) const{
	//FIXME aggheur set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if(set->isUsingWatches()){
		return new GenPWAgg(set);
	}else{
		return new ProdFWAgg(set);
	}
}

AggPropagator::AggPropagator(TypedSet* set)
		:set(set){

}

// Final initialization call!
void AggPropagator::initialize(bool& unsat, bool& sat) {
	for (agglist::const_iterator i = getSet().getAgg().begin(); i < getSet().getAgg().end(); ++i) {
		// FIXME permanent watches!
		if((*i)->getSem()==IMPLICATION){
			getSet().getPCSolver().acceptLitEvent(getSetp(), ~(*i)->getHead(), FAST);
		}else{
			getSet().getPCSolver().acceptLitEvent(getSetp(), (*i)->getHead(), FAST);
			getSet().getPCSolver().acceptLitEvent(getSetp(), ~(*i)->getHead(), FAST);
		}
	}
}

lbool AggPropagator::value(const Lit& l) const {
	return getSet().value(l);
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
