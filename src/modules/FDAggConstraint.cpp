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

using namespace MinisatID;

FDAggConstraint::FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<int>& weights,
		const Weight& bound)
		: 	Propagator(engine, "fdaggconstr"),
			head(head),
			type(getType(type)),
			vars(set),
			weights(weights),
			bound(bound) {
	getPCSolver().accept(this, head, FAST);
	getPCSolver().accept(this, not head, FAST);
	for (auto i = set.cbegin(); i != set.cend(); ++i) {
		getPCSolver().acceptBounds(*i, this);
	}
}

rClause FDAggConstraint::notifypropagate() {
	auto headval = value(head);
	int min = 0, max = 0;
	for (int i = 0; i < vars.size(); ++i) {
		auto weight = weights[i];
		auto minval = vars[i]->minValue();
		auto maxval = vars[i]->maxValue();
		if (weight < 0) {
			min += maxval * weight;
			max += minval * weight;
		} else {
			min += minval * weight;
			max += maxval * weight;
		}
	}
	if (headval == l_Undef) {
		if (min >= bound) {
			litlist minlits;
			for (int i = 0; i < vars.size(); ++i) {
				if (weights[i] < 0) {
					minlits.push_back(not vars[i]->getLEQLit(vars[i]->maxValue()));
				} else {
					minlits.push_back(not vars[i]->getGEQLit(vars[i]->minValue()));
				}
			}
			Disjunction clause(minlits);
			clause.literals.push_back(head);
			auto c = getPCSolver().createClause(clause, true);
			getPCSolver().addLearnedClause(c);
		} else if (max < bound) {
			litlist maxlits;
			for (int i = 0; i < vars.size(); ++i) {
				if (weights[i] < 0) {
					maxlits.push_back(not vars[i]->getGEQLit(vars[i]->minValue()));
				} else {
					maxlits.push_back(not vars[i]->getLEQLit(vars[i]->maxValue()));
				}
			}
			Disjunction clause(maxlits);
			clause.literals.push_back(not head);
			auto c = getPCSolver().createClause(clause, true);
			getPCSolver().addLearnedClause(c);
		}
	} else if (headval == l_True) {
		// for any var: var GEQ TOP(varmax-(totalmax-bound)/weight) TODO check
		for (int i = 0; i < vars.size(); ++i) {
			auto var = vars[i];
			auto val = var->maxValue() - (max - bound) / weights[i]; // FIXME rounding!
			auto geqlit = var->getGEQLit(val);
			if (value(geqlit) != l_True) {
				litlist lits;
				lits.push_back(not head);
				for (int j = 0; j < vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					if (weights[i] < 0) {
						lits.push_back(not vars[j]->getGEQLit(vars[j]->minValue()));
					} else {
						lits.push_back(not vars[j]->getLEQLit(vars[j]->maxValue()));
					}
				}
				lits.push_back(geqlit);
				Disjunction clause(lits);
				clause.literals.push_back(not head);
				auto c = getPCSolver().createClause(clause, true);
				if(value(geqlit)==l_False){ // Conflict
					return c;
				}else{
					getPCSolver().addLearnedClause(c);
				}
			}
		}
	} else { // head is false
		// for any var: var LEQ BOT(varmin+(bound-totalmin)/weight)-1 TODO check
		for (int i = 0; i < vars.size(); ++i) {
			auto var = vars[i];
			auto val = var->minValue() + (bound-min) / weights[i] -1; // FIXME rounding!
			auto leqlit = var->getLEQLit(val);
			if (value(leqlit) != l_True) {
				litlist lits;
				lits.push_back(not head);
				for (int j = 0; j < vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					if (weights[i] < 0) {
						lits.push_back(not vars[j]->getLEQLit(vars[j]->maxValue()));
					} else {
						lits.push_back(not vars[j]->getGEQLit(vars[j]->minValue()));
					}
				}
				lits.push_back(leqlit);
				Disjunction clause(lits);
				clause.literals.push_back(head);
				auto c = getPCSolver().createClause(clause, true);
				if(value(leqlit)==l_False){ // Conflict
					return c;
				}else{
					getPCSolver().addLearnedClause(c);
				}
			}
		}
	}
}
