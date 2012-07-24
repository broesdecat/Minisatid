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
			case EqType::L: //0<bound
				if (not 0 < bound) {
					unsat = true;
				}
				break;

			case EqType::LEQ: //0<bound
				if (not 0 <= bound) {
					unsat = true;
				}
				break;

			case EqType::G: //0<bound
				if (not 0 > bound) {
					unsat = true;
				}
				break;

			case EqType::GEQ: //0<bound
				if (not 0 >= bound) {
					unsat = true;
				}
				break;

			case EqType::EQ: //0<bound
				if (not 0 == bound) {
					unsat = true;
				}
				break;
			case EqType::EQ: //0<bound
				if (not 0 != bound) {
					unsat = true;
				}
				break;
			}
		}
		if (rel == EqType::EQ) {
			if (bound % combinedWeight != 0) {
				unsat = true;
			} else {
				bound = bound / combinedWeight;
				newweights = {1};
			}
		}
		else {
			//Convention: for products: always exactly one weight.
			newweights = {combinedWeight};
		}
		if (unsat) {
			engine->setTrue(-head, this); //FIXME explanation?
			notifyNotPresent();
		}
	}
	_head = head;
	_vars = newset;
	if (rel == EqType::EQ || rel == EqType::NEQ) {
		auto eq = (rel == EqType::EQ);
		auto one = mkPosLit(getPCSolver().newVar());
		auto two = mkPosLit(getPCSolver().newVar());
		internalAdd(Implication(eq ? head : not head, ImplicationType::EQUIVALENT, { one, two }, true), getPCSolver());
		_head = one;
		new FDAggConstraint(engine, two, type, _vars, newweights, EqType::LEQ, bound);
	}
	if (rel == EqType::L || rel == EqType::G) {
		_head = not head;
	}
	if (rel == EqType::G || rel == EqType::LEQ) {
		for (auto i = newweights.cbegin(); i < newweights.cend(); ++i) {
			//Due to the convention: for products: always exactly one weight, this also works for products
			_weights.push_back(-*i);
		}
		_bound = -bound;
	} else { // GEQ, EQ, NEQ, L
		_weights = newweights;
		_bound = bound;
	}

	/*cerr<<"Added fdconstraint " <<toString(_head) <<" <=> ";
	 for(uint i=0; i<_vars.size(); ++i) {
	 cerr <<_weights[i] <<"*var" <<_vars[i]->toString() <<" ";
	 }
	 cerr <<">= " <<_bound <<"\n";*/

	getPCSolver().accept(this, _head, FAST);
	getPCSolver().accept(this, not _head, FAST);
	for (auto i = _vars.cbegin(); i != _vars.cend(); ++i) {
		getPCSolver().acceptBounds(*i, this);
	}
	getPCSolver().acceptForPropagation(this);
	// TODO remove trivially true aggregates NOTE: done for products.
}

std::pair<int, int> FDAggConstraint::getMinAndMaxPossibleAggVals() const {
	if (_type == getType(AggType::SUM)) {
		int min = 0, max = 0;
		for (uint i = 0; i < _vars.size(); ++i) {
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
		return {min,max};
	} else if (_type == getType(AggType::PROD)) {
		int max = abs(_weights[0]);
		for (uint i = 0; i < _vars.size(); ++i) {
			auto absminval = abs(_vars[i]->minValue());
			auto absmaxval = abs(_vars[i]->maxValue());
			max *= (absmaxval>absminval?absmaxval:absminval);
		}
		return{-max,max}; //TODO: can be improved if no negative values are possible: {0,max}

	} else {
		throw notYetImplemented("FDAggconstraint for other things than sum and product");
		return {0,0};
	}
}

rClause FDAggConstraint::notifypropagate() {
	/*cerr <<"Propagating " <<toString(_head) <<" <=> ";
	 for(uint i=0; i<_vars.size(); ++i) {
	 cerr <<_weights[i] <<"*var" <<_vars[i]->toString() <<" ";
	 }
	 cerr <<">= " <<_bound <<"\n";*/
	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;

	//cerr <<"Min " <<min <<", max " <<max <<"\n";
	if (_headval == l_Undef) {
		if (_type == getType(AggType::SUM)) {
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
		} else if (_type == getType(AggType::PROD)) {
			if (min >= _bound || max < _bound) {
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

	}

	// Optimize to stop early
	if ((min >= _bound && _headval == l_True) || (max < _bound && _headval == l_False)) {
		return nullPtrClause;
	}
	//TODO FROM HERE for products

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

