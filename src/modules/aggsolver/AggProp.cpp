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

#include "satsolver/heuristics/Heuristics.hpp"

using namespace std;
using namespace MinisatID;

SATVAL Agg::reInitializeAgg() {
	auto confl = getSet()->getProp()->reInitialize();
	if(confl!=nullPtrClause){
		getSet()->getPCSolver().addConflictClause(confl);
	}
	return getSet()->getPCSolver().satState();
}

paggprop AggProp::max = paggprop(new MaxProp());
//paggprop AggProp::min = paggprop (new MinProp());
paggprop AggProp::sum = paggprop(new SumProp());
paggprop AggProp::card = paggprop(new CardProp());
paggprop AggProp::prod = paggprop(new ProdProp());

const AggProp * MinisatID::getType(AggType type) {
	switch (type) {
	case AggType::MAX:
		return AggProp::getMax();
		break;
	case AggType::SUM:
		return AggProp::getSum();
		break;
	case AggType::CARD:
		return AggProp::getCard();
		break;
	case AggType::PROD:
		return AggProp::getProd();
		break;
	default:
		throw idpexception("Encountered a bug in the code which transforms aggregates.\n");
	}
}

Weight AggProp::getMinPossible(const TypedSet& set) const {
	return getMinPossible(set.getWL());
}
Weight AggProp::getMaxPossible(const TypedSet& set) const {
	return getMaxPossible(set.getWL());
}

// NOTE: The internal weighted set is not the same as the weighted set in the propagatorfactory with the same id
// the difference is that this set is normalized to only contain positive weights. See also makeSumSetPositive in AggSet.hpp
Weight AggProp::getValue(const TypedSet& set) const {
	Weight total = getESV();
	for (auto i = set.getWL().cbegin(); i < set.getWL().cend(); ++i) {
		auto val = set.value((*i).getLit());
		MAssert(val!=l_Undef);

		if (val == l_True) {
			total = add(total, (*i).getWeight());
		}
	}
	return total;
}

bool SumProp::isMonotone(const Agg& agg, const Weight& w) const {
	return (agg.hasUB() && w < 0) || (!agg.hasUB() && w > 0);
}
bool SumProp::isMonotone(const TempAgg& agg, const Weight& w) const {
	return (agg.hasUB() && w < 0) || (!agg.hasUB() && w > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const Weight& ) const {
	// MAssert(w>=0); TODO Place back if w is needed
	return !agg.hasUB();
}
bool ProdProp::isMonotone(const TempAgg& agg, const Weight&) const {
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

Weight SumProp::getMinPossible(const std::vector<WL>& wls) const {
	Weight min = getESV();
	for (vwl::const_iterator j = wls.cbegin(); j < wls.cend(); ++j) {
		if ((*j).getWeight() < 0) {
			min = this->add(min, (*j).getWeight());
		}
	}
	return min;
}

Weight SumProp::getMaxPossible(const std::vector<WL>& wls) const {
	Weight max = getESV();
	for (vwl::const_iterator j = wls.cbegin(); j < wls.cend(); ++j) {
		if ((*j).getWeight() > 0) {
			max = this->add(max, (*j).getWeight());
		}
	}
	return max;
}

Weight SumProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, Weight& knownbound) const {
	if (one.getWeight() < two.getWeight()) {
		knownbound += one.getWeight();
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		knownbound += two.getWeight();
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

// MAX Prop

bool MaxProp::isMonotone(const Agg& agg, const Weight& w) const {
	const Weight& w2 = agg.getBound();
	return (agg.hasUB() && w2 <= w) || (!agg.hasUB());
}
bool MaxProp::isMonotone(const TempAgg& agg, const Weight& w) const {
	return (agg.hasUB() && agg.getBound() <= w) || (!agg.hasUB());
}

Weight MaxProp::getMinPossible(const std::vector<WL>&) const {
	return getESV();
}

Weight MaxProp::getMaxPossible(const std::vector<WL>& wls) const {
	Weight max = getESV();
	for (vwl::const_iterator j = wls.cbegin(); j < wls.cend(); ++j) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight MaxProp::getCombinedWeight(const Weight& first, const Weight& second) const {
	return first > second ? first : second;
}

WL MaxProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, Weight& knownbound) const {
	if (one.getWeight() > two.getWeight()) {
		if (knownbound < two.getWeight()) {
			knownbound = two.getWeight();
		}
		return one;
	} else {
		if (knownbound < one.getWeight()) {
			knownbound = one.getWeight();
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
//	for(vwl::const_iterator j = set.getWL().cbegin(); j<set.getWL().cend(); ++j){
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
Weight ProdProp::getMinPossible(const std::vector<WL>&) const {
	return getESV();
}

Weight ProdProp::getMaxPossible(const std::vector<WL>& wls) const {
	Weight max = getESV();
	for (vwl::const_iterator j = wls.cbegin(); j < wls.cend(); ++j) {
		if ((*j).getWeight() > 0) {
			max = this->add(max, (*j).getWeight());
		}
	}
	return max;
}

Weight ProdProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef NOARBITPREC
	bool sign = false;
	Weight l = lhs, r = rhs;
	if (l < 0) {
		l = -l;
		sign = true;
	}
	if (r < 0) {
		r = -r;
		sign = !sign;
	}
	if (l != 0 && posInfinity() / l < r) {
		return sign ? negInfinity() : posInfinity();
	}
#endif
	return lhs * rhs;
}

Weight ProdProp::remove(const Weight&, const Weight&) const {
	throw idpexception("Cannot remove weights from a product propagator.\n");
}
Weight ProdProp::removeMin(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	MAssert(rhs!=0);
	//FIXME should prevent this from happening
	if (rhs != 0) {
		w = lhs / rhs;
		if (w * rhs > lhs) {
			w -= Weight(1);
		}
	}
	//clog <<"mindiv: " <<lhs <<"/" <<rhs <<"=" <<w <<"\n";
	return w;
}
Weight ProdProp::removeMax(const Weight& lhs, const Weight& rhs) const {
	Weight w = 0;
	MAssert(rhs!=0);
	//FIXME should prevent this from happening
	if (rhs != 0) {
		w = lhs / rhs;
		if (rhs * w < lhs) {
			w += Weight(1);
		}
	}
//	clog <<"maxdiv: " <<lhs <<"/" <<rhs <<"=" <<w <<"\n";
	return w;
}

Weight ProdProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL ProdProp::handleOccurenceOfBothSigns(const WL&, const WL&, Weight&) const {
	//NOTE: om dit toe te laten, ofwel bij elke operatie op en literal al zijn voorkomens overlopen
	//ofwel aggregaten voor doubles ondersteunen (hAggPropagatoret eerste is eigenlijk de beste oplossing)
	//Mogelijke eenvoudige implementatie: weigts bijhouden als doubles (en al de rest als ints)
	//FIXME cannot print this here NoSupportForBothSignInProductAgg(clog, one.getLit(), two.getLit());
	throw idpexception("Atoms in product aggregates have to be unique.\n");
}

//AGGREGATES

bool satisfies(const Weight& min, const Weight& max, bool ub, const Weight& certainbound){
	if (ub) {
		return max <= certainbound;
	} else { //LB
		return min >= certainbound;
	}
}

bool MinisatID::isSatisfied(const TempAgg& agg, const Weight& min, const Weight& max) {
	return satisfies(min, max, agg.hasUB(), agg.getBound());
}

bool MinisatID::isSatisfied(const TempAgg& agg, const minmaxBounds& bounds) {
	return isSatisfied(agg, bounds.min, bounds.max);
}

bool MinisatID::isFalsified(const TempAgg& agg, const Weight& min, const Weight& max) {
	if (agg.hasUB()) {
		return min > agg.getBound();
	} else { //LB
		return max < agg.getBound();
	}
}

bool MinisatID::isFalsified(const TempAgg& agg, const minmaxBounds& bounds) {
	return isFalsified(agg, bounds.min, bounds.max);
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
void MinisatID::addValue(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds) {
	addValue(type, weight, addtoset, bounds.min, bounds.max);
}
void MinisatID::addValue(const AggProp& type, const Weight& weight, bool addtoset, Weight& min, Weight& max) {
	bool pos = weight >= 0;
	if (pos && addtoset) {
		min = type.add(min, weight);
	} else if (pos && !addtoset) {
		max = type.removeMax(max, weight);
	} else if (!pos && addtoset) {
		max = type.add(max, weight);
	} else { //!pos && !addtoset
		min = type.removeMin(min, weight);
	}
}

void MinisatID::removeValue(const AggProp& type, const Weight& weight, bool wasinset, minmaxBounds& bounds) {
	removeValue(type, weight, wasinset, bounds.min, bounds.max);
}

void MinisatID::removeValue(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max) {
	bool pos = weight >= 0;
	if (pos && wasinset) {
		min = type.removeMin(min, weight);
	} else if (pos && !wasinset) {
		max = type.add(max, weight);
	} else if (!pos && wasinset) {
		max = type.removeMax(max, weight);
	} else { //!pos && !wasinset
		min = type.add(min, weight);
	}
}

// TypedSet

bool printedwarning = false;

AggPropagator* MaxProp::createPropagator(TypedSet* set) const {
	if (set->isUsingWatches() && !printedwarning) {
		clog << ">> Currently max/min aggregates never use watched-literal-schemes.\n";
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

AggPropagator* SumProp::createPropagator(TypedSet* set) const {
	// NOTE: guaranteerd to have only positive weights

	//FIXME aggheur set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if (set->isUsingWatches()) {
		return new GenPWAgg(set);
	} else {
		return new SumFWAgg(set);
	}
}

AggPropagator* ProdProp::createPropagator(TypedSet* set) const {
	// NOTE: guaranteerd to have only positive weights

	//FIXME aggheur set->getSolver()->adaptAggHeur(set->getWL(), set->getAgg().size());

	if (set->isUsingWatches()) {
		return new GenPWAgg(set);
	} else {
		return new ProdFWAgg(set);
	}
}

AggPropagator::AggPropagator(TypedSet* set)
		: set(set) {

}

const PCSolver& AggPropagator::getPCSolver() const {
	return getSet().getPCSolver();
}

// Final initialization call!
void AggPropagator::initialize(bool& unsat, bool& sat) {
	internalInitialize(unsat, sat);

	bool watchcomp = dynamic_cast<const FWAgg*>(this)!=NULL;
			//FIXME fully watched aggregates are bugged if the other watch is not added, even with implication, because the explanation generation builds on both heads being watched

	for (auto i = getSet().getAgg().cbegin(); i < getSet().getAgg().cend(); ++i) {
		// both for implication and comp
		auto w = new Watch(getSetp(), not (*i)->getHead(), *i, false);
		getSet().getPCSolver().accept(w);
		getSet().getPCSolver().notifyDecisionVar(var(w->getPropLit()));

		if ((*i)->getSem() == AggSem::COMP || watchcomp) {
			auto w2 = new Watch(getSetp(), (*i)->getHead(), *i, false);
			getSet().getPCSolver().accept(w2);
			getSet().getPCSolver().notifyDecisionVar(var(w->getPropLit()));
		}
		// TODO check the effect on performance of addheadImpl, card2Equiv and bumpVar of agg heads in AggPropagator::initialize
		getSet().getPCSolver().getHeuristic().notifyAggPropInit(var((*i)->getHead()));
	}
}

lbool AggPropagator::value(const Lit& l) const {
	return getSet().value(l);
}

void AggPropagator::propagate(Watch* ws) {
	int level = getSet().getPCSolver().getLevel(var(ws->getPropLit()));
	if (ws->headWatch()) {
		propagate(level, ws, ws->getAggIndex());
	} else {
		propagate(ws->getPropLit(), ws, level);
	}
}
