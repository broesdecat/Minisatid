/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/FDAggConstraint.hpp"
#include <iostream>
#include "utils/Print.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include <cmath>

using namespace std;
using namespace MinisatID;

FDAggConstraint::FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights,
		EqType rel, const Weight& bound)
		: 	Propagator(engine, "fdaggconstr"),
			_type(getType(type)) {
	Weight newbound = bound;
	MAssert(type == AggType::SUM || type==AggType::PROD);
	std::vector<IntView*> newset;
	std::vector<Weight> newweights;
	if (_type == getType(AggType::SUM)) {
		for (uint i = 0; i < set.size(); ++i) {
			bool found = false;
			for (uint j = 0; j < newset.size(); ++j) {
				if (set[i]->id() == newset[j]->id()) {
					newweights[j] += weights[i]; //distributivity //FIXME overflows!
					found = true;
					break;
				}
			}
			if (not found) {
				newset.push_back(set[i]);
				newweights.push_back(weights[i]);
			}
		}
		auto si = newset.begin();
		auto wi = newweights.begin();
		for (; si < newset.end();) {
			if ((*wi) == Weight(0)) {
				si = newset.erase(si);
				wi = newweights.erase(wi);

			} else {
				++si;
				++wi;
			}
		}
	} else if (_type == getType(AggType::PROD)) {
		newset = set;
		Weight combinedWeight = Weight(1);
		for (uint i = 0; i < weights.size(); ++i) {
			combinedWeight *= weights[i]; //FIXME overflows!
		}
		bool unsat = false;
		if (combinedWeight == 0) {
			switch (rel) {
			case EqType::L: //0<newbound
				if (not 0 < newbound) {
					unsat = true;
				}
				break;

			case EqType::LEQ: //0<newbound
				if (not 0 <= newbound) {
					unsat = true;
				}
				break;

			case EqType::G: //0<newbound
				if (not 0 > newbound) {
					unsat = true;
				}
				break;

			case EqType::GEQ: //0<newbound
				if (not 0 >= newbound) {
					unsat = true;
				}
				break;

			case EqType::EQ: //0<newbound
				if (not 0 == newbound) {
					unsat = true;
				}
				break;
			case EqType::NEQ: //0<newbound
				if (not 0 != newbound) {
					unsat = true;
				}
				break;
			}
			notifyNotPresent();
		}
		if (rel == EqType::EQ) {
			if (newbound % combinedWeight != 0) {
				unsat = true;
			} else {
				newbound = newbound / combinedWeight;
				newweights = {1};
			}
		}
		else {
			//Convention: for products: always exactly one weight.
			newweights = {combinedWeight};
		}
		if (unsat) {
			engine->setTrue(not head, this); //FIXME explanation?
			notifyNotPresent();
		}
	}
	_head = head;
	_vars = newset;
	if (rel == EqType::EQ || rel == EqType::NEQ) {
		auto eq = (rel == EqType::EQ);
		auto one = mkPosLit(getPCSolver().newVar());
		auto two = mkPosLit(getPCSolver().newVar());
		internalAdd(Implication(eq ? head : not head, ImplicationType::EQUIVALENT, { one, two }, true), getPCSolver()); //Head equiv one and two
		_head = one;
		new FDAggConstraint(engine, two, type, _vars, newweights, EqType::LEQ, newbound);
	}
	if (rel == EqType::L || rel == EqType::G) {
		_head = not head;
	}
	if (rel == EqType::G || rel == EqType::LEQ) {
		for (auto i = newweights.cbegin(); i < newweights.cend(); ++i) {
			//Due to the convention: for products: always exactly one weight, this also works for products
			_weights.push_back(-*i);
		}
		_bound = -newbound;
	} else { // GEQ, EQ, NEQ, L
		_weights = newweights;
		_bound = newbound;
	}

	getPCSolver().accept(this, _head, FAST);
	getPCSolver().accept(this, not _head, FAST);
	for (auto i = _vars.cbegin(); i != _vars.cend(); ++i) {
		getPCSolver().acceptBounds(*i, this);
	}
	getPCSolver().acceptForPropagation(this);
	// TODO remove trivially true aggregates NOTE: done for products.
}

//NOTE: for products, this does not include the weight!!!
std::pair<int, int> FDAggConstraint::getMinAndMaxPossibleAggValsWithout(int varloc) const {
	if (_type == getType(AggType::SUM)) {
		int min = 0, max = 0;
		for (uint i = 0; i < _vars.size(); ++i) {
			if (i != varloc) {
				auto weight = _weights[i];
				auto minval = _vars[i]->minValue();
				auto maxval = _vars[i]->maxValue();
				if (weight < 0) {
					min += maxval * weight;
					max += minval * weight;
				} else {
					min += minval * weight;
					max += maxval * weight;
				}
			}
		}
		return {min,max};
	} else if (_type == getType(AggType::PROD)) {
		if (containsNegatives()) {
			int max = 1;
			for (uint i = 0; i < _vars.size(); ++i) {
				if (i != varloc) {
					auto absminval = abs(_vars[i]->minValue());
					auto absmaxval = abs(_vars[i]->maxValue());
					max *= (absmaxval > absminval ? absmaxval : absminval);
				}
			}
			return {-max,max};
		} else {
			int min = 1, max = 1;
			for (uint i = 0; i < _vars.size(); ++i) {
				if (i != varloc) {
					auto minval = _vars[i]->minValue();
					auto maxval = _vars[i]->maxValue();
					min *= minval;
					max *= maxval;
				}
			}
			return {min,max};
		}
	} else {
		throw notYetImplemented("FDAggconstraint for other things than sum and product");
		return {0,0};
	}
}
std::pair<int, int> FDAggConstraint::getMinAndMaxPossibleAggVals() const {
	return getMinAndMaxPossibleAggValsWithout(-1);
}

bool FDAggConstraint::containsNegatives() const {
	for (uint i = 0; i < _vars.size(); ++i) {
		auto var = _vars[i];
		auto lit = var->getGEQLit(0);
		if (value(lit) != l_True) {
			return true;
		}
	}
	return false;
}

rClause FDAggConstraint::notifypropagateSum() {
	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;

	if (_headval == l_Undef) {
		if (min >= _bound) {
			litlist minlits;
			minlits.push_back(_head);
			for (uint i = 0; i < _vars.size(); ++i) {
				if (_weights[i] < 0) {
					minlits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				} else {
					minlits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				}
			}
			auto c = getPCSolver().createClause(Disjunction(minlits), true);
			getPCSolver().addLearnedClause(c);
		} else if (max < _bound) {
			litlist maxlits;
			maxlits.push_back(not _head);
			for (uint i = 0; i < _vars.size(); ++i) {
				if (_weights[i] < 0) {
					maxlits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				} else {
					maxlits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				}
			}
			auto c = getPCSolver().createClause(Disjunction(maxlits), true);
			getPCSolver().addLearnedClause(c);
		}
		return nullPtrClause;
	}

	// Optimize to stop early
	if ((min >= _bound && _headval == l_True) || (max < _bound && _headval == l_False)) {
		return nullPtrClause;
	}

	if (_headval == l_True) {
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			Lit lit;
			if (_weights[i] > 0) {
				// var >= TOP((bound - (max-weight*varmax))/weight)
				auto val = ceil((_bound - (max - _weights[i] * var->maxValue())) / (double) _weights[i]);
				lit = var->getGEQLit(val);
			} else {
				// var =< BOT((bound - (max-weight*varmin))/weight)
				auto val = floor((_bound - (max - _weights[i] * var->minValue())) / (double) _weights[i]);
				lit = var->getLEQLit(val);
			}
			if (value(lit) != l_True) {
				litlist lits;
				lits.push_back(not _head);
				for (uint j = 0; j < _vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					if (_weights[j] < 0) {
						lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
					} else {
						lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
					}
				}
				lits.push_back(lit);
				auto c = getPCSolver().createClause(Disjunction(lits), true);
				if (value(lit) == l_False) { // Conflict
					getPCSolver().addConflictClause(c);
					return c;
				} else {
					getPCSolver().addLearnedClause(c);
				}
			}
		}

	} else { // _head is false
		// for any var:
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			Lit lit;

			if (_weights[i] > 0) {
				// var =< BOT((bound - (min-weight*varmin))/weight)
				auto val = (_bound - (min - _weights[i] * var->minValue())) / (double) _weights[i];
				if (val == floor(val)) {
					val--;
				} else {
					val = floor(val);
				}
				lit = var->getLEQLit(val);
			} else {
				// var >= TOP((bound - (min-weight*varmax))/weight+0.01)
				auto val = ((_bound - (min - _weights[i] * var->maxValue())) / (double) _weights[i]);
				if (val == ceil(val)) {
					val++;
				} else {
					val = ceil(val);
				}
				lit = var->getGEQLit(val);
			}
			if (value(lit) != l_True) {
				litlist lits;
				lits.push_back(_head);
				for (uint j = 0; j < _vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					if (_weights[j] < 0) {
						lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
					} else {
						lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
					}
				}
				lits.push_back(lit);
				auto c = getPCSolver().createClause(Disjunction(lits), true);
				if (value(lit) == l_False) { // Conflict
					getPCSolver().addConflictClause(c);
					return c;
				} else {
					getPCSolver().addLearnedClause(c);
				}
			}
		}
	}
	return nullPtrClause;
}

rClause FDAggConstraint::notifypropagateProd() {
	if (containsNegatives()) {
		return notifypropagateProdWithNeg();
	}
	return notifypropagateProdWithoutNeg();
}
rClause FDAggConstraint::notifypropagateProdWithoutNeg() {
	//FIXME Divides by zero!
	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;
	MAssert(_weights.size() == 1 && _weights[0] != 0);
	//Constructor should guarantee this.
	double realbound = _bound / (double) _weights[0];

	bool reverse = (_weights[0] < 0);
	//if -1 * Prod{x_i} >= bound, then Prod{x_i} =< -bound

	if (_headval == l_Undef) {
		litlist lits;
		if (min >= realbound && not reverse) {
			lits.push_back(_head);
			for (uint i = 0; i < _vars.size(); ++i) {
				lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
			}
		} else if (max < realbound && not reverse) {
			lits.push_back(not _head);
			for (uint i = 0; i < _vars.size(); ++i) {
				lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
			}
		} else if (max <= realbound && reverse) {
			lits.push_back(_head);
			for (uint i = 0; i < _vars.size(); ++i) {
				lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
			}
		} else if (min > realbound && reverse) {
			lits.push_back(not _head);
			for (uint i = 0; i < _vars.size(); ++i) {
				lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
			}
		}
		if (not lits.empty()) {
			auto c = getPCSolver().createClause(Disjunction(lits), true);
			getPCSolver().addLearnedClause(c);
		}
		return nullPtrClause;
	}
	// Optimize to stop early
	if (not reverse && ((min >= realbound && _headval == l_True) || (max < realbound && _headval == l_False))) {
		return nullPtrClause;
	}
	if (reverse && ((max <= realbound && _headval == l_True) || (min > realbound && _headval == l_False))) {
		return nullPtrClause;
	}
	if (_headval == l_True) {
		// Optimize to stop early
		if (not reverse && realbound <= 0) {
			return nullPtrClause;
		}
		if (not reverse) {
			if (max == 0) {
				MAssert(min == 0);
				//calculation
				MAssert(min<realbound);
				//early stop condition
				MAssert(realbound > 0);
				//consequence of two above
				//Special case, max is 0, thus either realbound must be 0 or every var must be greater than 0.
				//but realbound cant be 0
				for (uint i = 0; i < _vars.size(); ++i) {
					auto var = _vars[i];
					auto lit = var->getGEQLit(1);
					auto c = getPCSolver().createClause(Disjunction( { not _head, lit }), true);
					if (value(lit) == l_False) { // Conflict
						getPCSolver().addConflictClause(c);
						return c;
					} else {
						getPCSolver().addLearnedClause(c);
					}
				}
				return nullPtrClause;
			}
			//Normal case: max != 0, hence also every var.maxvalue != 0
			//PROD{x_i} >= realbound
			for (uint i = 0; i < _vars.size(); ++i) {
				auto var = _vars[i];
				double varmax = var->maxValue();
				MAssert(varmax != 0);
				double maxWithoutThisVar = max / varmax;
				MAssert(maxWithoutThisVar != 0);
				int factorMissing = ceil(realbound / maxWithoutThisVar);
				auto lit = var->getGEQLit(factorMissing);

				if (value(lit) != l_True) {
					litlist lits;
					lits.push_back(not _head);
					for (uint j = 0; j < _vars.size(); ++j) {
						if (j == i) {
							continue;
						}
						lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
					}
					lits.push_back(lit);
					auto c = getPCSolver().createClause(Disjunction(lits), true);
					if (value(lit) == l_False) { // Conflict
						getPCSolver().addConflictClause(c);
						return c;
					} else {
						getPCSolver().addLearnedClause(c);
					}
				}
			}
		} else {
			//PROD{x_i} <= realbound

			for (uint i = 0; i < _vars.size(); ++i) {
				auto var = _vars[i];
				double varmin = var->minValue();
				double minWithoutThisVar = varmin == 0 ? getMinAndMaxPossibleAggValsWithout(i).first : min / varmin;
				if (minWithoutThisVar == 0) {
					continue;
				}
				int factorMaxLeft = floor(realbound / minWithoutThisVar);
				auto lit = var->getLEQLit(factorMaxLeft);
				if (value(lit) != l_True) {
					litlist lits;
					lits.push_back(not _head);
					for (uint j = 0; j < _vars.size(); ++j) {
						if (j == i) {
							continue;
						}
						lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
					}
					lits.push_back(lit);
					auto c = getPCSolver().createClause(Disjunction(lits), true);
					if (value(lit) == l_False) { // Conflict
						getPCSolver().addConflictClause(c);
						return c;
					} else {
						getPCSolver().addLearnedClause(c);
					}
				}
			}
		}
	} else { // _head is false
		if (not reverse) {
			//Propagate PROD{x_i} < realbound
			for (uint i = 0; i < _vars.size(); ++i) {
				auto var = _vars[i];
				double varmin = var->minValue();
				double minWithoutThisVar = varmin == 0 ? getMinAndMaxPossibleAggValsWithout(i).first : min / varmin;
				if (minWithoutThisVar == 0) {
					continue;
				}
				auto val = realbound / minWithoutThisVar;
				if (val == floor(val)) {
					val--; //Because we can only get LEQlit
				} else {
					val = floor(val);
				}
				Lit lit = var->getLEQLit(val);

				if (value(lit) != l_True) {
					litlist lits;
					lits.push_back(_head);
					for (uint j = 0; j < _vars.size(); ++j) {
						if (j == i) {
							continue;
						}
						lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
					}
					lits.push_back(lit);
					auto c = getPCSolver().createClause(Disjunction(lits), true);
					if (value(lit) == l_False) { // Conflict
						getPCSolver().addConflictClause(c);
						return c;
					} else {
						getPCSolver().addLearnedClause(c);
					}
				}
			}
		} else {
			if (max == 0) {
				MAssert(min == 0);
				//calculation
				MAssert(min<=realbound);
				//early stop condition
				MAssert(realbound >= 0);
				//consequence of two above
				//Special case, max is 0, thus either realbound must be 0 or every var must be greater than 0.
				if (realbound != 0) {
					for (uint i = 0; i < _vars.size(); ++i) {
						auto var = _vars[i];
						auto lit = var->getGEQLit(1);
						auto c = getPCSolver().createClause(Disjunction( { not _head, lit }), true);
						if (value(lit) == l_False) { // Conflict
							getPCSolver().addConflictClause(c);
							return c;
						} else {
							getPCSolver().addLearnedClause(c);
						}
					}
				}
				return nullPtrClause;
			}
			//Propagate PROD{x_i} > realbound
			for (uint i = 0; i < _vars.size(); ++i) {
				auto var = _vars[i];
				auto maxWithoutThisVar = max / var->maxValue();
				auto val = realbound / maxWithoutThisVar;
				if (val == ceil(val)) {
					val++; //Because we can only get GEQlit
				} else {
					val = ceil(val);
				}
				Lit lit = var->getGEQLit(val);

				if (value(lit) != l_True) {
					litlist lits;
					lits.push_back(_head);
					for (uint j = 0; j < _vars.size(); ++j) {
						if (j == i) {
							continue;
						}
						lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
					}
					lits.push_back(lit);
					auto c = getPCSolver().createClause(Disjunction(lits), true);
					if (value(lit) == l_False) { // Conflict
						getPCSolver().addConflictClause(c);
						return c;
					} else {
						getPCSolver().addLearnedClause(c);
					}
				}
			}
		}
	}
	return nullPtrClause;
}
rClause FDAggConstraint::notifypropagateProdWithNeg() {

	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();

	int min = minmax.first;
	int max = minmax.second;
	double realbound = _bound / (double) _weights[0];
	//TODO:  incorporate the sign of weights[0]!!!!!!!!!
	//TODO:  divide by 0
	throw notYetImplemented("products with neg");

	if (_headval == l_Undef) {
		if (min >= realbound || max < realbound) {
			litlist minlits;
			minlits.push_back(_head);
			for (uint i = 0; i < _vars.size(); ++i) {
				auto absminval = abs(_vars[i]->minValue());
				auto absmaxval = abs(_vars[i]->maxValue());
				auto absbiggest = absminval > absmaxval ? absminval : absmaxval;
				minlits.push_back(not _vars[i]->getLEQLit(-absbiggest));
				minlits.push_back(not _vars[i]->getGEQLit(absbiggest));
			}
			auto c = getPCSolver().createClause(Disjunction(minlits), true);
			getPCSolver().addLearnedClause(c);
		}

	}

	// Optimize to stop early
	if ((min >= realbound && _headval == l_True) || (max < realbound && _headval == l_False)) {
		return nullPtrClause;
	}

	if ((_headval == l_True && realbound >= 0) || (_headval == l_False && realbound <= 0)) {
		//PROD { x_1.. x_n } >= realbound THUS: we implement abs(PROD { x_1.. x_n }) >= k.
		//We can only derive useful information if realbound is positive.

		//SECOND CASE:
		//PROD { x_1.. x_n } < realbound
		//We only propagate for negative realbound. In that case, we propagate Abs(Prod) >= Abs(realbound)

		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			auto maxWithoutThisVar1 = abs(max / var->maxValue());
			auto maxWithoutThisVar2 = abs(max / var->minValue());
			auto maxWithoutThisVar = maxWithoutThisVar1 > maxWithoutThisVar2 ? maxWithoutThisVar2 : maxWithoutThisVar1;
			//maxWithoutThisVar is smallest of the two since the biggest value of var.maxval and var.minval was added
			auto stillNeeded = ceil(abs(realbound / maxWithoutThisVar));
			Lit bigger = var->getGEQLit(stillNeeded);
			Lit smaller = var->getGEQLit(-stillNeeded);
			if (value(bigger) != l_True && value(smaller) != l_True) {
				litlist lits;
				lits.push_back(_headval == l_True ? not _head : _head);
				for (uint j = 0; j < _vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					auto absminval = abs(_vars[i]->minValue());
					auto absmaxval = abs(_vars[i]->maxValue());
					auto absbiggest = absminval > absmaxval ? absminval : absmaxval;
					lits.push_back(not _vars[i]->getLEQLit(-absbiggest));
					lits.push_back(not _vars[i]->getGEQLit(absbiggest));
				}
				lits.push_back(bigger);
				lits.push_back(smaller);

				auto c = getPCSolver().createClause(Disjunction(lits), true);
				if (value(bigger) == l_False && value(smaller) == l_False) { // Conflict
					getPCSolver().addConflictClause(c);
					return c;
				} else {
					getPCSolver().addLearnedClause(c);
				}
			}
		}
	}

	return nullPtrClause;
}

rClause FDAggConstraint::notifypropagate() {
	if (_type == getType(AggType::SUM)) {
		return notifypropagateSum();
	} else {
		return notifypropagateProd();
	}
}
