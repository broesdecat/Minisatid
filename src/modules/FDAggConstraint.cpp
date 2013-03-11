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
#include "utils/NumericLimits.hpp"
#include "IntVar.hpp"
#include "utils/SafeInt.hpp"

using namespace std;
using namespace MinisatID;

IntView* FDAggConstraint::negation(IntView* bound) {
	auto result = createBound(-bound->maxValue(), -bound->minValue());
	auto head = getPCSolver().newVar();
	auto headIsTrue = mkPosLit(head);
	getPCSolver().setTrue(headIsTrue, this); //FIXME: explanation
	const int& zero = 0; //doing this here, to make the disambiguation.
	new FDAggConstraint(getID(), &getPCSolver(), headIsTrue, AggType::SUM, { bound, result }, { 1, 1 }, EqType::GEQ, zero);
	new FDAggConstraint(getID(), &getPCSolver(), headIsTrue, AggType::SUM, { bound, result }, { -1, -1 }, EqType::GEQ, zero);
	if (verbosity() > 5) {
		clog << toString(head) << " <=> var" << toString(result->getVarID()) << " + var" << toString(bound->getVarID()) << " = 0" << endl;
	}
	//We cannot use equality here, since that would cause loops...
	return result;
}

IntView* FDAggConstraint::createBound(const Weight& min, const Weight& max) {
	IntVar* newvar = NULL;
	if(abs(max-min)<100){ // FIXME duplicate heuristic in Propagatorfactory
		newvar = new RangeIntVar(getID(), &getPCSolver(), getPCSolver().newID(), min, max);
	}else{
		newvar = new LazyIntVar(getID(), &getPCSolver(), getPCSolver().newID(), min, max);
	}
	newvar->finish();
	return new IntView(newvar, 0);
}

void FDAggConstraint::sharedInitialization(AggType type, PCSolver* engine, const Lit& head, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, IntView* bound) {
	//FIXME .. PASS THE ID
	_head = head;
	_vars = set;
	if (rel == EqType::EQ || rel == EqType::NEQ) {
		auto eq = (rel == EqType::EQ);
		auto one = mkPosLit(getPCSolver().newVar());
		auto two = mkPosLit(getPCSolver().newVar());
		add(Implication(getID(), eq ? head : not head, ImplicationType::EQUIVALENT, { one, two }, true));
		if (verbosity() > 5) {
			clog << "split FDAggConstraint with head " << toString(head) << " into GEQ with head " << toString(one) << " and LEQ with head " << toString(two)
					<< endl;
			clog << toString(eq ? head : not head) << " <=> " << toString(one) << " && " << toString(two) << endl;
		}
		_head = one;
		if (type == AggType::PROD) {
			new FDAggConstraint(getID(), engine, two, type, _vars, weights.front(), EqType::LEQ, bound);
		} else {
			new FDAggConstraint(getID(), engine, two, type, _vars, weights, EqType::LEQ, bound);
		}
	}
	if (rel == EqType::L || rel == EqType::G) {
		_head = not head;
	}
	if (rel == EqType::G || rel == EqType::LEQ) {
		for (auto i = weights.cbegin(); i < weights.cend(); ++i) {
			//Due to the convention: for products: always exactly one weight, this also works for products
			_weights.push_back(-*i);
		}
		_bound = negation(bound);
	} else { // GEQ, EQ, NEQ, L, now all transformed to GEQ
		_weights = weights;
		_bound = bound;
	}

	getPCSolver().accept(this, _head, FAST);
	getPCSolver().accept(this, not _head, FAST);
	for (auto i = _vars.cbegin(); i != _vars.cend(); ++i) {
		getPCSolver().acceptBounds(*i, this);
	}
	getPCSolver().acceptBounds(_bound, this);
	getPCSolver().acceptForPropagation(this);
	// TODO remove trivially true aggregates
}

bool additionOverflow(int x, int y) {
	if (((double) x) + y > getMaxElem<int>()) {
		return true;
	}
	if (((double) x) + y < getMinElem<int>()) {
		return true;
	}
	return false;
}

FDAggConstraint::FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights,
		EqType rel, const Weight& bound)
		: Propagator(id, engine, "fdaggconstr"), _type(getType(type)) {
	MAssert(type==AggType::SUM && weights.size()==set.size());
	initializeSum(engine, head, set, weights, rel, createBound(bound, bound));
}

FDAggConstraint::FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights,
		EqType rel, IntView* bound)
		: Propagator(id, engine, "fdaggconstr"), _type(getType(type)) {
	MAssert(type==AggType::SUM && weights.size()==set.size());
	initializeSum(engine, head, set, weights, rel, bound);
}
void FDAggConstraint::initializeSum(PCSolver* engine, const Lit& head, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
		IntView* bound) {
	// Handle duplicate variables by adding their weights
	std::vector<IntView*> newset;
	std::vector<Weight> newweights;
	for (uint i = 0; i < set.size(); ++i) {
		bool found = false;
		for (uint j = 0; j < newset.size(); ++j) {
			if (set[i]->getVarID() == newset[j]->getVarID()) {
				if (additionOverflow(newweights[j], weights[i])) {
					throw idpexception("Overflow in weights of fd sum constraint");
				}
				newweights[j] += weights[i];
				found = true;
				break;
			}
		}
		if (not found) {
			newset.push_back(set[i]);
			newweights.push_back(weights[i]);
		}
	}

	// Remove all weights "0"
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

	SafeInt<Weight> absmax(0); //note that s == 0 unless set
	try {
		for(uint i=0; i<newset.size(); ++i){
			SafeInt<Weight> sumterm(newweights[i]);
			sumterm *= max(abs(newset[i]->maxValue()), abs(newset[i]->minValue()));
			absmax += sumterm;
		}
	} catch (const SafeIntException& err) {
		throw idpexception("Overflow possible for sum of a set of variables in limited integer precision.");
	}

	sharedInitialization(AggType::SUM, engine, head, newset, newweights, rel, bound);
}

FDAggConstraint::FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const Weight& weight, EqType rel,
		const Weight& bound)
		: Propagator(id, engine, "fdaggconstr"), _type(getType(type)) {
	MAssert(type==AggType::PROD);
	initializeProd(engine, head, set, weight, rel, createBound(bound, bound));
}

FDAggConstraint::FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const Weight& weight, EqType rel,
		IntView* bound)
		: Propagator(id, engine, "fdaggconstr"), _type(getType(type)) {
	MAssert(type==AggType::PROD);
	initializeProd(engine, head, set, weight, rel, bound);
}
void FDAggConstraint::initializeProd(PCSolver* engine, const Lit& head, const std::vector<IntView*>& set, const Weight& weight, EqType rel, IntView* bound) {
	if (weight == 0) {
		new FDAggConstraint(getID(), engine, head, AggType::SUM, { bound }, { 1 }, invertEqType(rel), weight);
		notifyNotPresent();
		return;
	}

	SafeInt<Weight> absmax(abs(weight)); //note that s == 0 unless set
	try {
		for (auto var : set) {
			absmax *= max(abs(var->maxValue()), abs(var->minValue()));
		}
	} catch (const SafeIntException& err) {
		throw idpexception("Overflow possible for a product of a set of variables in limited integer precision.");
	}

	sharedInitialization(AggType::PROD, engine, head, set, { weight }, rel, bound);
}

rClause FDAggConstraint::notifypropagate() {
	if (_type == getType(AggType::SUM)) {
		return notifypropagateSum();
	} else {
		MAssert(_type == getType(AggType::PROD));
		return notifypropagateProd();
	}
}

rClause FDAggConstraint::notifypropagateSum() {
	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;
	MAssert(_bound->minValue()==_bound->maxValue());
	auto bound = _bound->minValue();
	if (_headval == l_Undef) {
		if (min >= bound) {
			litlist minlits;
			minlits.push_back(_head);
			for (uint i = 0; i < _vars.size(); ++i) {
				if (_weights[i] < 0) {
					minlits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				} else {
					minlits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				}
			}
			auto c = getPCSolver().createClause(Disjunction(getID(), minlits), true);
			getPCSolver().addLearnedClause(c);
		} else if (max < bound) {
			litlist maxlits;
			maxlits.push_back(not _head);
			for (uint i = 0; i < _vars.size(); ++i) {
				if (_weights[i] < 0) {
					maxlits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				} else {
					maxlits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				}
			}
			auto c = getPCSolver().createClause(Disjunction(getID(), maxlits), true);
			getPCSolver().addLearnedClause(c);
		}
		return nullPtrClause;
	}

	// Optimize to stop early
	if ((min >= bound && _headval == l_True) || (max < bound && _headval == l_False)) {
		return nullPtrClause;
	}

	if (_headval == l_True) {
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			Lit lit;
			if (_weights[i] > 0) {
				// var >= TOP((bound - (max-weight*varmax))/weight)
				auto val = ceil((bound - (max - _weights[i] * var->maxValue())) / (double) _weights[i]);
				lit = var->getGEQLit(val);
			} else {
				// var =< BOT((bound - (max-weight*varmin))/weight)
				auto val = floor((bound - (max - _weights[i] * var->minValue())) / (double) _weights[i]);
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
				auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
				if (value(lit) == l_False) { // Conflict
					getPCSolver().addConflictClause(c);
					return c;
				} else {
					getPCSolver().addLearnedClause(c);
					return nullPtrClause;
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
				auto val = (bound - (min - _weights[i] * var->minValue())) / (double) _weights[i];
				if (val == floor(val)) {
					val--;
				} else {
					val = floor(val);
				}
				lit = var->getLEQLit(val);
			} else {
				// var >= TOP((bound - (min-weight*varmax))/weight+0.01)
				auto val = ((bound - (min - _weights[i] * var->maxValue())) / (double) _weights[i]);
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
				auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
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
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;
	int minbound = _bound->minValue();
	int maxbound = _bound->maxValue();
	bool boundKnown = (minbound == maxbound);

	if (min == max && boundKnown) {
		return checkProduct(min, minbound);
	}

	return nullPtrClause;

	if (canContainNegatives()) {
		return nullPtrClause;
		//return notifypropagateProdWithNeg(min, max, minbound, maxbound);
	}
	return notifypropagateProdWithoutNeg(min, max, minbound, maxbound);
}

rClause FDAggConstraint::checkProduct(int val, int boundvalue) {
	auto headval = value(_head);

	litlist lits;
	if ((val * _weights[0]) >= boundvalue) {
		if (headval == l_True) {
			return nullPtrClause;
		}
		lits.push_back(_head);

	} else {
		if (headval == l_False) {
			return nullPtrClause;
		}
		lits.push_back(not _head);
	}

	//We want to construct: current situation implies (head or not head, depending on previous context)

	auto extralit = not _bound->getLEQLit(boundvalue);
	MAssert(value(extralit)==l_False);
	lits.push_back(extralit);
	extralit = not _bound->getGEQLit(boundvalue);
	MAssert(value(extralit)==l_False);
	lits.push_back(extralit);

	//TODO: In case one of the variable is equal to zero, better explanation can be made
	for (uint i = 0; i < _vars.size(); ++i) {
		auto extralit = not _vars[i]->getLEQLit(_vars[i]->maxValue());
		MAssert(value(extralit)==l_False);
		lits.push_back(extralit);
		extralit = not _vars[i]->getGEQLit(_vars[i]->minValue());
		MAssert(value(extralit)==l_False);
		lits.push_back(extralit);
	}
	auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
	if (value(lits[0]) == l_False) { // Conflict
		getPCSolver().addConflictClause(c);
		return c;
	} else {
		getPCSolver().addLearnedClause(c);
	}
	return nullPtrClause;
}


litlist FDAggConstraint::notAllVarsArePositive(){
	litlist lits;
	for (uint i = 0; i < _vars.size(); ++i) {
		lits.push_back(_vars[i]->getLEQLit(-1));
	}
	return lits;
}

rClause FDAggConstraint::notifypropagateProdWithoutNeg(int mini, int maxi, int minbound, int maxbound) {
	auto headval = value(_head);

	MAssert(_weights.size() == 1 && _weights[0] != 0);
	//Constructor should guarantee this.

	int realmax = max(mini * _weights[0], maxi * _weights[0]);
	int realmin = min(mini * _weights[0], maxi * _weights[0]);
	bool reverted = (_weights[0] < 0); //whether or not the min and max values have changed place

	//First propagation: Aggregate and bound -> head
	if (headval == l_Undef) {
		litlist lits = notAllVarsArePositive();
		bool propagate = false;
		if (realmin >= maxbound) {
			propagate = true;
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
			//List all vars that have had a contribution to realmin
			for (uint i = 0; i < _vars.size(); ++i) {
				if (not reverted) {
					lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				} else {
					lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				}
			}
		} else if (realmax < minbound) {
			propagate = true;
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));
			//List all vars that have had a contribution to realmax
			for (uint i = 0; i < _vars.size(); ++i) {
				if (not reverted) {
					lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				} else {
					lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				}
			}
		}
		if (propagate) {
			auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
			getPCSolver().addLearnedClause(c);
		}
		return nullPtrClause;
	}
	// Optimize to stop early
	if (((realmin >= maxbound && headval == l_True) || (realmax < minbound && headval == l_False))) {
		return nullPtrClause;
	}

	//PROPAGATION 2: HEAD -> AGG AND BOUND
	//CASE: HEAD == TRUE
	if (headval == l_True) {
		//PROPAGATE: agg >= bound

		MAssert(realmin < maxbound);
		//We know realmin < maxbound because of early stop condition

		// Optimize to stop early
		if ((not reverted && maxbound <= 0)) {
			return nullPtrClause;
		}
		//PROPAGATION 2a: head and agg to bound
		//[realmin,realmax] >= [minbound,maxbound]
		//Thus, we can eliminate all bounds greater than realmax
		if (realmax < maxbound) {
			litlist lits = notAllVarsArePositive();
			lits.push_back(not _head);
			//List all vars that have had a contribution to realmax
			for (uint i = 0; i < _vars.size(); ++i) {
				if (not reverted) {
					lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				} else {
					lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				}
			}
			auto boundlit = _bound->getLEQLit(realmax);
			lits.push_back(boundlit);
			auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
			if (value(boundlit) == l_False) {
				getPCSolver().addConflictClause(c);
				return c;
			} else {
				getPCSolver().addLearnedClause(c);
				return nullPtrClause;
			}
		}

		//PROPAGATION 2b: head and bound to agg
		//PROD{x_i} >= [minbound,maxbound], hence certainly Prod{x_i} >= minbound, we implemant realmax >=minbound
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			auto varusedval = reverted ? var->minValue() : var->maxValue(); //The value that has been used for var to calculate realmax
			double maxWithoutThisVar;
			if (varusedval == 0) {
				MAssert(realmax == 0);
				auto minmaxnovar = getMinAndMaxPossibleAggValsWithout(i);
				maxWithoutThisVar = max(minmaxnovar.first * _weights[0], minmaxnovar.second * _weights[0]);
			} else {
				maxWithoutThisVar = realmax / (double) varusedval;
			}
			if (maxWithoutThisVar == 0) {
				//no propagation, this var cannot change anything.
				continue;
			}
			int factormissing;
			if (not reverted) {
				factormissing = ceil(minbound / maxWithoutThisVar);
			} else {
				factormissing = floor(minbound / maxWithoutThisVar);
			}
			Lit lit;
			if (not reverted) {
				lit = var->getGEQLit(factormissing);
			} else {
				lit = var->getLEQLit(factormissing);
			}

			if (value(lit) != l_True) {
				litlist lits = notAllVarsArePositive();
				lits.push_back(not _head);
				lits.push_back(not _bound->getGEQLit(minbound));
				//List all vars that have had a contribution to realmax
				for (uint j = 0; j < _vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					if (reverted) {
						lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
					} else {
						lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
					}
				}
				lits.push_back(lit);
				auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
				if (value(lit) == l_False) { // Conflict
					getPCSolver().addConflictClause(c);
					return c;
				} else {
					getPCSolver().addLearnedClause(c);
					return nullPtrClause;
				}
			}
		}
	} //PROPAGATION 2: HEAD -> AGG AND BOUND
	  //CASE: HEAD == FALSE
	else {
		//PROPAGATE: agg < bound

		MAssert(realmax >= minbound);
		//We know realmax >= minbound  because of early stop condition

		// Optimize to stop early
		if ((reverted && minbound >= 0)) {
			return nullPtrClause;
		}
		//PROPAGATION 2a: head and agg to bound
		//[realmin,realmax] < [minbound,maxbound]
		//Thus, we can eliminate all bounds smaller than realmin
		if (realmin > minbound) {
			litlist lits = notAllVarsArePositive();
			lits.push_back(_head);
			//List all vars that have had a contribution to realmin
			for (uint i = 0; i < _vars.size(); ++i) {
				if (reverted) {
					lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
				} else {
					lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
				}
			}
			auto boundlit = _bound->getGEQLit(realmin);
			lits.push_back(boundlit);
			auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
			if(value(boundlit) == l_False){
				getPCSolver().addConflictClause(c);
				return c;
			}else{
				MAssert(value(boundlit)==l_Undef);
				getPCSolver().addLearnedClause(c);
				return nullPtrClause;
			}
		}

		//PROPAGATION 2b: head and bound to agg
		//PROD{x_i} < [minbound,maxbound], hence certainly Prod{x_i} < maxbound, we implement realmin < maxbound
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			auto varusedval = reverted ? var->maxValue() : var->minValue(); //The value that has been used for var to calculate realmmin
			double minWithoutThisVar;
			if (varusedval == 0) {
				MAssert(realmin == 0);
				auto minmaxnovar = getMinAndMaxPossibleAggValsWithout(i);
				minWithoutThisVar = min(minmaxnovar.first * _weights[0], minmaxnovar.second * _weights[0]);
			} else {
				minWithoutThisVar = realmin / (double) varusedval;
			}
			if (minWithoutThisVar == 0) {
				//no propagation, this var cannot change anything.
				continue;
			}
			double maxFactorThisVar = maxbound / minWithoutThisVar;
			if (not reverted) {
				if (maxFactorThisVar == floor(maxFactorThisVar)) {
					maxFactorThisVar--; //Because we can only get LEQlit
				} else {
					maxFactorThisVar = floor(maxFactorThisVar);
				}
			} else {
				if (maxFactorThisVar == ceil(maxFactorThisVar)) {
					maxFactorThisVar++; //Because we can only get GEQlit
				} else {
					maxFactorThisVar = ceil(maxFactorThisVar);
				}
			}
			Lit lit;
			if (reverted) {
				lit = var->getGEQLit(maxFactorThisVar);
			} else {
				lit = var->getLEQLit(maxFactorThisVar);
			}

			if (value(lit) != l_True) {
				litlist lits = notAllVarsArePositive();
				lits.push_back(_head);
				lits.push_back(not _bound->getLEQLit(maxbound));
				//List all vars that have had a contribution to realmin
				for (uint j = 0; j < _vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					if (reverted) {
						lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
					} else {
						lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
					}
				}
				lits.push_back(lit);
				auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
				if (value(lit) == l_False) { // Conflict
					getPCSolver().addConflictClause(c);
					return c;
				} else {
					getPCSolver().addLearnedClause(c);
					return nullPtrClause;
				}
			}
		}
	}
	return nullPtrClause;
}

void FDAggConstraint::getLitsNotCurrentAbsValSituation(litlist& lits, uint excludedvarloc) {
	//List all vars that have had a contribution to realmax
	for (uint i = 0; i < _vars.size(); ++i) {
		if (i == excludedvarloc) {
			continue;
		}
		auto absminval = abs(_vars[i]->minValue());
		auto absmaxval = abs(_vars[i]->maxValue());
		auto absbiggest = max(absminval, absmaxval);
		lits.push_back(not _vars[i]->getGEQLit(-absbiggest));
		lits.push_back(not _vars[i]->getLEQLit(absbiggest));
	}
}

rClause FDAggConstraint::notifypropagateProdWithNeg(int minval, int maxval, int minbound, int maxbound) {
	auto headval = value(_head);

	int realmax = abs(max(minval * _weights[0], maxval * _weights[0]));
	int realmin = -realmax;

	//PROPAGATION 1: from agg and bound to head
	if (headval == l_Undef) {
		litlist lits;
		if (realmin >= maxbound) {
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
		} else if (realmax < minbound) {
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));
		}
		if (lits.size() != 0) {
			getLitsNotCurrentAbsValSituation(lits, _vars.size());
			//Propagation has occured. This can NEVER be a conflict, since we can always choose the value of head appropriately.
			auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
			getPCSolver().addLearnedClause(c);
		}
		return nullPtrClause;
	}

	// Optimize to stop early
	if (((realmin >= maxbound && headval == l_True) || (realmax < minbound && headval == l_False))) {
		return nullPtrClause;
	}
	//PROPAGATION 2: HEAD AND AGG -> BOUND
	if (headval == l_True) {
		if (realmax < maxbound) {
			MAssert(_bound->maxValue() == maxbound);
			litlist lits;
			lits.push_back(not _head);
			//List all vars that have had a contribution to realmax
			getLitsNotCurrentAbsValSituation(lits, _vars.size());
			auto boundlit = _bound->getLEQLit(realmax);
			lits.push_back(boundlit);
			auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
			if(value(boundlit ) ==l_False){
				getPCSolver().addConflictClause(c);
				return c;
			}
			else{
				MAssert(value(boundlit)==l_Undef);
				getPCSolver().addLearnedClause(c);
				return nullPtrClause;
			}
		}
	} else if (headval == l_False) {
		//PROD < bound
		if (realmin > minbound) {
			litlist lits;
			lits.push_back(_head);
			//List all vars that have had a contribution to realmin
			getLitsNotCurrentAbsValSituation(lits, _vars.size());
			auto boundlit = _bound->getGEQLit(realmin);
			lits.push_back(boundlit);
			auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
			if(value(boundlit ) ==l_False){
				getPCSolver().addConflictClause(c);
				return c;
			}
			else{
				MAssert(value(boundlit)==l_Undef);
				getPCSolver().addLearnedClause(c);
				return nullPtrClause;
			}
		}
	}

	//PROPAGATION 3: HEAD AND BOUND -> AGG
	bool attemptPropagation3 = false;
	Weight propagationbound = 0;
	Lit propagationlit;
	if (headval == l_True) {
		// ABS(PROD { x_1.. x_n }) >= [minbound,maxbound], hence we can only propagate
		if (minbound >= 0) {
			attemptPropagation3 = true;
			propagationbound = minbound;
			propagationlit = not _bound->getGEQLit(minbound);
			// We can propagate on ABS(PROD { x_1.. x_n }) >= propagationbound
		}
	}
	if (headval == l_False && maxbound <= 0) {
		attemptPropagation3 = true;
		// We can handle PROD { x_1.. x_n } < maxbound with a negative bound
		// by propagating ABS(PROD { x_1.. x_n }) >= ABS(maxbound)+1
		propagationbound = Weight((-1 * maxbound) + 1);
		propagationlit = not _bound->getLEQLit(maxbound);
	}

	if (attemptPropagation3) {
		//Now in any case, we should propagate Abs(Prod) >= realbound
		// For each var, we remove it from the still possible interval and check whether that would violate the bound
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			auto absvarmax = max(abs(var->maxValue()), abs(var->minValue()));

			MAssert(absvarmax != 0);
			// NOTE: otherwise product was already decided
			auto maxWithoutThisVar = abs(realmax / absvarmax);
			MAssert(maxWithoutThisVar != 0);
			auto stillNeeded = ceil(abs(propagationbound / maxWithoutThisVar));

			bool propagate = false;
			bool conflict = false;
			litlist lits;

			auto bigger = var->getGEQLit(stillNeeded);
			auto smaller = var->getLEQLit(-stillNeeded);
			if (value(bigger) != l_True && value(smaller) != l_True) {
				propagate = true;
				lits.push_back(bigger);
				lits.push_back(smaller);
				conflict = (value(bigger) == l_False && value(smaller) == l_False);
			}

			if (propagate) {
				// We construct the clause:
				// In this situation (for all variables) with this head: propagate that abs(var) should be at least "stillneeded"
				lits.push_back(headval == l_True ? not _head : _head);
				lits.push_back(propagationlit);
				for (uint j = 0; j < _vars.size(); ++j) {
					if (j == i) {
						continue;
					}
					auto absminval = abs(_vars[j]->minValue());
					auto absmaxval = abs(_vars[j]->maxValue());
					auto absbiggest = max(absminval, absmaxval);
					auto lit = not _vars[j]->getLEQLit(absbiggest);
					MAssert(value(lit) == l_False);
					lits.push_back(lit);
					lit = not _vars[j]->getGEQLit(-absbiggest);
					MAssert(value(lit) == l_False);
					lits.push_back(lit);
				}

				auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
				if (conflict) {
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

//NOTE: for products, this does not include the weight!!! and also... This is an estimate.
// varloc might not exist!
std::pair<int, int> FDAggConstraint::getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const {
	if (_type == getType(AggType::SUM)) {
		int min = 0, max = 0;
		for (uint i = 0; i < _vars.size(); ++i) {
			if (i == excludedVar) {
				continue;
			}
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
	} else {
		MAssert(_type == getType(AggType::PROD));
		if (canContainNegatives()) {
			int absmax = 1;
			int decidedval = 1;
			bool decided = true;
			for (uint i = 0; i < _vars.size(); ++i) {
				if (i == excludedVar) {
					continue;
				}
				auto minval = _vars[i]->minValue();
				auto maxval = _vars[i]->maxValue();
				if (decided && minval == maxval) {
					decidedval *= maxval;
				} else {
					decided = false;
				}
				absmax *= max(abs(maxval), abs(minval));
			}
			if (decided) {
				return {decidedval,decidedval};
			}
			return {-absmax,absmax};
		} else {
			int min = 1, max = 1;
			for (uint i = 0; i < _vars.size(); ++i) {
				if (i != excludedVar) {
					auto minval = _vars[i]->minValue();
					auto maxval = _vars[i]->maxValue();
					min *= minval;
					max *= maxval;
				}
			}
			return {min,max};
		}
	}
}
std::pair<int, int> FDAggConstraint::getMinAndMaxPossibleAggVals() const {
	return getMinAndMaxPossibleAggValsWithout(_vars.size());
}

bool FDAggConstraint::canContainNegatives() const {
	for (auto i = _vars.cbegin(); i < _vars.cend(); ++i) {
		if ((*i)->minValue() < 0) {
			return true;
		}
	}
	return false;
}
