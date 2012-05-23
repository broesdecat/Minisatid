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

using namespace std;
using namespace MinisatID;

FDAggConstraint::FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights,
		EqType rel, const Weight& bound)
		: 	Propagator(engine, "fdaggconstr"),
			_type(getType(type)) {

	_head = head;
	_vars = set;
	if(rel==EqType::EQ){
		new FDAggConstraint(engine, head, type, set, weights, EqType::LEQ, bound);
	}else if(rel==EqType::NEQ){
		_head = not head;
		new FDAggConstraint(engine, not head, type, set, weights, EqType::LEQ, bound);
	}
	if(rel==EqType::L || rel==EqType::G){
		_head = not head;
	}
	if(rel==EqType::G || rel==EqType::LEQ){
		for(auto i=weights.cbegin(); i<weights.cend(); ++i){
			_weights.push_back(-*i);
		}
		_bound = -bound;
	}else{ // GEQ, EQ, NEQ, L
		_weights = weights;
		_bound = bound;
	}

	getPCSolver().accept(this, _head, FAST);
	getPCSolver().accept(this, not _head, FAST);
	for (auto i = set.cbegin(); i != set.cend(); ++i) {
		getPCSolver().acceptBounds(*i, this);
	}
}

rClause FDAggConstraint::notifypropagate() {
	auto _headval = value(_head);
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
	} else if (_headval == l_True) {
		// for any var: var GEQ TOP(varmax-(totalmax-_bound)/weight) TODO check
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			Lit lit;
			if (_weights[i] > 0) {
				auto val = var->maxValue() - (max - _bound) / _weights[i]; // FIXME rounding!
				lit = var->getGEQLit(val);
			} else {
				auto val = var->minValue() + (max - _bound) / -_weights[i]; // FIXME rounding!
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
		// for any var: var LEQ BOT(varmin+(_bound-totalmin)/weight)-1 TODO check
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			Lit lit;
			if (_weights[i] > 0) {
				auto val = var->minValue() + (_bound - min) / _weights[i] - 1; // FIXME rounding!
				lit = var->getLEQLit(val);
			} else {
				auto val = var->maxValue() + (_bound - min) / -_weights[i] - 1; // FIXME rounding!
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
