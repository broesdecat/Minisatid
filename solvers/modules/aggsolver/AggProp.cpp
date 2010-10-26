/*
 * AggProp.cpp
 *
 *  Created on: Oct 26, 2010
 *      Author: broes
 */

#include <limits>
#include "solvers/modules/aggsolver/AggProp.hpp"

using namespace std;
using namespace MinisatID;

typedef numeric_limits<int> intlim;

bool MaxProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() <= agg.getLowerBound()) || (agg.isUpper());
}

bool SumProp::isMonotone(const Agg& agg, const WL& l) const {
	return (agg.isLower() && l.getWeight() < 0) || (agg.isUpper() && l.getWeight() > 0);
}

bool ProdProp::isMonotone(const Agg& agg, const WL& l) const {
	assert(l.getWeight() == 0 || l.getWeight() >= 1);
	return agg.isUpper();
}

Weight SumProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && intlim::max()-lhs < rhs) {
		return intlim::max();
	} else if(lhs<0 && rhs<0 && intlim::min()-lhs>rhs) {
		return intlim::min();
	}
#endif
	return lhs + rhs;
}

Weight SumProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight SumProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight SumProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL SumProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	if (one.getWeight() < two.getWeight()) {
		set->setESV(set->getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setESV(set->getESV() + two.getWeight());
		return WL(one.getLit(), this->remove(one.getWeight(), two.getWeight()));
	}
}

///////
// CARD Prop
///////

Weight CardProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight CardProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	if(lhs>0 && rhs > 0 && intlim::max()-lhs < rhs) {
		return intlim::max();
	} else if(lhs<0 && rhs<0 && intlim::min()-lhs>rhs) {
		return intlim::min();
	}
#endif
	return lhs + rhs;
}

Weight CardProp::remove(const Weight& lhs, const Weight& rhs) const {
	return lhs - rhs;
}

Weight CardProp::getCombinedWeight(const Weight& one, const Weight& two) const {
	return this->add(one, two);
}

WL CardProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	if (one.getWeight() < two.getWeight()) {
		set->setESV(set->getESV() + one.getWeight());
		return WL(two.getLit(), this->remove(two.getWeight(), one.getWeight()));
	} else {
		set->setESV(set->getESV() + two.getWeight());
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

WL MaxProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
	if (one.getWeight() > two.getWeight()) {
		if (set->getESV() < two.getWeight()) {
			set->setESV(two.getWeight());
		}
		return one;
	} else {
		if (set->getESV() < one.getWeight()) {
			set->setESV(one.getWeight());
		}
		return two;
	}
}

///////
// PROD Prop
///////

Weight ProdProp::getBestPossible(TypedSet* set) const {
	Weight max = set->getESV();
	for (vwl::const_iterator j = set->getWL().begin(); j < set->getWL().end(); j++) {
		max = this->add(max, (*j).getWeight());
	}
	return max;
}

Weight ProdProp::add(const Weight& lhs, const Weight& rhs) const {
#ifdef INTWEIGHT
	bool sign = false;
	Weight l = lhs, r = rhs;
	if(l<0) {
		l= -l;
		sign = true;
	}
	if(r<0) {
		r = -r;
		sign = !sign;
	}
	if(intlim::max()/l < r) {
		return sign?intlim::min():intlim::max();
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

WL ProdProp::handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) {
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
