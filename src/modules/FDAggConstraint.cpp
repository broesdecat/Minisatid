/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
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

FDAggConstraint::FDAggConstraint(uint id, PCSolver* s, const std::string& name)
		: Propagator(id, s, name) {
}

IntView* FDAggConstraint::negation(IntView* bound) {
	auto result = createBound(-bound->maxValue(), -bound->minValue());
	auto head = getPCSolver().newAtom();
	auto headIsTrue = mkPosLit(head);
	auto t = getPCSolver().getTrueLit();
	getPCSolver().setTrue(headIsTrue, this); //FIXME: explanation
	const int& zero = 0; //doing this here, to make the disambiguation.
	new FDSumConstraint(getID(), &getPCSolver(), headIsTrue, { t, t }, { bound, result }, { 1, 1 }, EqType::GEQ, zero);
	new FDSumConstraint(getID(), &getPCSolver(), headIsTrue, { t, t }, { bound, result }, { -1, -1 }, EqType::GEQ, zero);
	if (verbosity() > 5) {
		clog << toString(head) << " <=> var" << toString(result->getVarID()) << " + var" << toString(bound->getVarID()) << " = 0" << endl;
	}
	//We cannot use equality here, since that would cause loops...
	return result;
}

IntView* FDAggConstraint::createBound(const Weight& min, const Weight& max) {
	IntVar* newvar = NULL;
	if (abs(max - min) < 100) { // FIXME duplicate heuristic in Propagatorfactory
		newvar = new RangeIntVar(getID(), &getPCSolver(), getPCSolver().newID(), min, max);
	} else {
		newvar = new LazyIntVar(getID(), &getPCSolver(), getPCSolver().newID(), min, max);
	}
	newvar->finish();
	return new IntView(newvar, 0);
}

void FDAggConstraint::sharedInitialization(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, IntView* bound) {
	//FIXME .. PASS THE ID
	if (set.size() == 0) {
		int neutral = 0;
		if (getType() == AggType::PROD) {
			MAssert(weights.size() == 1);
			neutral = weights[0];
		}
		//HEAD <=> neutral (* weight) rel bound
		//Thus, we should get the bound rel neutral lit and invert it in case rel is not EQ or NEQ
		auto condition = bound->getCompareLit(neutral, rel);
		if (rel != EqType::EQ && rel != EqType::NEQ) {
			condition = !condition;
		}
		add(Implication(getID(), head, ImplicationType::EQUIVALENT, { condition }, true));
		if (verbosity() > 5) {
			clog << "Set was empty, FDAGGConstraint simplified to:";
			clog << toString(head) << " <=> " << toString(condition) << endl;
		}
		return;
	}
	_head = head;
	_vars = set;
	if (rel == EqType::EQ || rel == EqType::NEQ) {
		auto eq = (rel == EqType::EQ);
		auto one = mkPosLit(getPCSolver().newAtom());
		auto two = mkPosLit(getPCSolver().newAtom());
		add(Implication(getID(), eq ? head : not head, ImplicationType::EQUIVALENT, { one, two }, true));
		if (verbosity() > 5) {
			clog << "split FDAggConstraint with head " << toString(head) << " into GEQ with head " << toString(one) << " and LEQ with head " << toString(two)
					<< endl;
			clog << toString(eq ? head : not head) << " <=> " << toString(one) << " && " << toString(two) << endl;
		}
		_head = one;
		if (getType() == AggType::PROD) {
			new FDProdConstraint(getID(), &getPCSolver(), two, conditions, _vars, weights.front(), EqType::LEQ, bound);
		} else {
			MAssert(getType() == AggType::SUM);
			new FDSumConstraint(getID(), &getPCSolver(), two, conditions, _vars, weights, EqType::LEQ, bound);
		}
	}
	if (rel == EqType::L || rel == EqType::G) {
		_head = not head;
	}

	if (rel == EqType::G || rel == EqType::LEQ) {
		std::vector<Weight> negatedWeights;
		for (auto i = weights.cbegin(); i < weights.cend(); ++i) {
			//Due to the convention: for products: always exactly one weight, this also works for products
			negatedWeights.push_back(-*i);
		}
		setWeights(negatedWeights);
		_bound = negation(bound);
	} else { // GEQ, EQ, NEQ, L, now all transformed to GEQ
		setWeights(weights);
		_bound = bound;
	}

	_conditions = conditions;

	getPCSolver().accept(this, _head, FAST);
	getPCSolver().accept(this, not _head, FAST);
	for (auto i = _vars.cbegin(); i != _vars.cend(); ++i) {
		getPCSolver().acceptBounds(*i, this);
	}
	for (auto c : _conditions) {
		getPCSolver().accept(this, c, FAST);
		getPCSolver().accept(this, not c, FAST);
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

std::pair<int, int> FDAggConstraint::getMinAndMaxPossibleAggVals() const {
	return getMinAndMaxPossibleAggValsWithout(_vars.size());
}

litlist FDAggConstraint::varsContributingToMax() const {
	return varsContributingToMax(_vars.size());
}
litlist FDAggConstraint::varsContributingToMin() const {
	return varsContributingToMin(_vars.size());
}

bool FDAggConstraint::canContainNegatives() const {
	for (uint j = 0; j < _vars.size(); j++) {
		if (value(_conditions[j]) == l_False) {
			continue;
		}
		if (_vars[j]->minValue() < 0) {
			return true;
		}
	}
	return false;
}

/**
 * Adds the disjunction of lits to the solver and returns the clause
 * If criticalLit is false, this is a conflict-clause
 * otherwise, a learned clause
 */
rClause FDAggConstraint::addClause(litlist& lits, bool conflict) {
	auto c = getPCSolver().createClause(Disjunction(getID(), lits), true);
	if (conflict) { // Conflict
		getPCSolver().addConflictClause(c);
		return c;
	} else {
		getPCSolver().addLearnedClause(c);
		return nullPtrClause;
	}
}

/*
 * SUMS
 */

void FDSumConstraint::setWeights(const std::vector<Weight>& w) {
	_weights = w;
}

void FDSumConstraint::initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights,
		EqType rel, IntView* bound) {
	// Handle duplicate variables by adding their weights
	std::vector<IntView*> newset;
	std::vector<Weight> newweights;
	std::vector<Lit> newConditions;
	for (uint i = 0; i < set.size(); ++i) {
		bool found = false;
		for (uint j = 0; j < newset.size(); ++j) {
			if (set[i]->getVarID() == newset[j]->getVarID()) {
				if (conditions[i].x == newConditions[j].x) {
					Weight weightToAdd = weights[i];
					if (conditions[i].hasSign() == newConditions[j].hasSign()) {
						weightToAdd = -weightToAdd;
					}
					if (additionOverflow(newweights[j], weightToAdd)) {
						throw idpexception("Overflow in weights of fd sum constraint");
					}
					newweights[j] += weights[i];
					found = true;
					break;
				}
			}
		}
		if (not found) {
			newset.push_back(set[i]);
			newweights.push_back(weights[i]);
			newConditions.push_back(conditions[i]);
		}
	}

	// Remove all weights "0", or false conditions
	auto si = newset.begin();
	auto wi = newweights.begin();
	auto ci = newConditions.begin();

	for (; si < newset.end();) {
		if ((*wi) == Weight(0) || value(*ci) == l_False) {
			si = newset.erase(si);
			wi = newweights.erase(wi);
			ci = newConditions.erase(ci);
		} else {
			++si;
			++wi;
			++ci;
		}
	}

	SafeInt<Weight> absmax(0); //note that s == 0 unless set
	try {
		for (uint i = 0; i < newset.size(); ++i) {
			SafeInt<Weight> sumterm(newweights[i]);
			sumterm *= max(abs(newset[i]->maxValue()), abs(newset[i]->minValue()));
			absmax += sumterm;
		}
	} catch (const SafeIntException& err) {
		throw idpexception("Overflow possible for sum of a set of variables in limited integer precision.");
	}
	sharedInitialization(head, newConditions, newset, newweights, rel, bound);
}

FDSumConstraint::FDSumConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, const Weight& bound)
		: FDAggConstraint(id, engine, "fdsumconstr") {
	MAssert(weights.size()==set.size());
	MAssert(conditions.size()==set.size());
	initialize(head, conditions, set, weights, rel, createBound(bound, bound));
}

FDSumConstraint::FDSumConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, IntView* bound)
		: FDAggConstraint(id, engine, "fdsumconstr") {
	MAssert(weights.size()==set.size());
	initialize(head, conditions, set, weights, rel, bound);
}

std::pair<int, int> FDSumConstraint::getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const {
	int min = 0, max = 0;
	for (uint i = 0; i < _vars.size(); ++i) {
		if (i == excludedVar) {
			//Variable has no influence as he should be excluded
			continue;
		}
		if (value(_conditions[i]) == l_False) {
			//Variable has no influence as his conditions is false
			continue;
		}

		auto weight = _weights[i];
		auto minval = _vars[i]->minValue();
		auto maxval = _vars[i]->maxValue();
		if (value(_conditions[i]) != l_True) {
			//conditions i is possibly false
			minval = minval < 0 ? minval : 0;
			maxval = maxval > 0 ? maxval : 0;
		}
		if (weight < 0) {
			min += maxval * weight;
			max += minval * weight;
		} else {
			min += minval * weight;
			max += maxval * weight;
		}
	}
	return {min,max};
}

/**
 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
 * But excludes the excludedVar'th variable
 */
litlist FDSumConstraint::varsContributingToMax(size_t excludedVar) const {
	litlist lits;
	for (uint j = 0; j < _vars.size(); ++j) {
		if (j == excludedVar) {
			continue;
		}
		if (value(_conditions[j]) == l_False) {
			lits.push_back(_conditions[j]);
		} else {
			if (value(_conditions[j]) == l_True) {
				lits.push_back(not _conditions[j]);
			}
			if (_weights[j] < 0) {
				lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
			} else {
				lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
			}
		}
	}
	return lits;
}
litlist FDSumConstraint::varsContributingToMin(size_t excludedVar) const {
	litlist lits;
	for (uint j = 0; j < _vars.size(); ++j) {
		if (j == excludedVar) {
			continue;
		}
		if (value(_conditions[j]) == l_False) {
			lits.push_back(_conditions[j]);
		} else {
			if (value(_conditions[j]) == l_True) {
				lits.push_back(not _conditions[j]);
			}
			if (_weights[j] < 0) {
				lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
			} else {
				lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
			}
		}
	}
	return lits;
}

rClause FDSumConstraint::notifypropagate() {
	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;

	MAssert(_bound->minValue()==_bound->maxValue());
	auto bound = _bound->minValue();

	//Propagation AGG =>  head
	if (_headval == l_Undef) {
		if (min >= bound) {
			auto minlits = FDAggConstraint::varsContributingToMin();
			minlits.push_back(_head);
			addClause(minlits, false);
		} else if (max < bound) {
			auto maxlits = FDAggConstraint::varsContributingToMax();
			maxlits.push_back(not _head);
			addClause(maxlits, false);
		}
		return nullPtrClause;
	}

	// Optimize to stop early
	if ((min >= bound && _headval == l_True) || (max < bound && _headval == l_False)) {
		return nullPtrClause;
	}
	for (uint i = 0; i < _vars.size(); ++i) {
		auto var = _vars[i];
		auto weight = _weights[i];
		//Calculate max and min without this var: this method is more efficient than doing the entire
		//Calculation again.
		int maxWithoutThisVar = max;
		int minWithoutThisVar = min;
		if (value(_conditions[i]) != l_False) {
			auto minval = var->minValue();
			auto maxval = var->maxValue();
			if (value(_conditions[i]) != l_True) {
				//conditions i is possibly false
				minval = minval < 0 ? minval : 0;
				maxval = maxval > 0 ? maxval : 0;
			}
			if (weight < 0) {
				minWithoutThisVar -= maxval * weight;
				maxWithoutThisVar -= minval * weight;
			} else {
				minWithoutThisVar -= minval * weight;
				maxWithoutThisVar -= maxval * weight;
			}
		}
		if (_headval == l_True) {
			Lit lit;
			bool notBeingZeroIsRelevant = false;
			if (value(_conditions[i]) == l_False) {
				//In this case, we can only derive a possible conflict:
				if (max < bound) {
					auto lits = varsContributingToMax(i);
					lits.push_back(not _head);
					lits.push_back(_conditions[i]);
					return addClause(lits, true);
				} else {
					continue;
				}
			} else {
				//In this case we can do more precise reasoning on the bound:
				//calculate max of aggreagate without this variable
				//exclude all values of this var that do not succeed in making this big enough
				// We know: w_i*v_i >= (b-minWithout(i))
				if (weight > 0) {
					// var >= TOP((bound - maxWithout)/weight)
					auto val = ceil((bound - maxWithoutThisVar) / (double) weight);
					lit = var->getGEQLit(val);
					notBeingZeroIsRelevant = (val > 0);
				} else {
					// var =< BOT((bound - maxWithout)/weight)
					auto val = floor((bound - maxWithoutThisVar) / (double) weight);
					lit = var->getLEQLit(val);
					notBeingZeroIsRelevant = (val < 0);
				}
			}
			if (value(_conditions[i]) == l_Undef && notBeingZeroIsRelevant) {
				auto maxlits = varsContributingToMax(i);
				maxlits.push_back(not _head);
				//(otherMax & head) => _condition
				maxlits.push_back(_conditions[i]);
				addClause(maxlits, false);
				//Can NEVER cause a conflict as _c[i] == l_Undef
			}
			//We can only propagate something about the value of term i if its condition is true (or propagated to be true)
			bool propagateValue = notBeingZeroIsRelevant || value(_conditions[i]) == l_True;
			if (propagateValue && value(lit) != l_True) {
				//Some values not yet excluded
				auto maxlits = varsContributingToMax(i);
				maxlits.push_back(not _head);
				maxlits.push_back(not _conditions[i]);
				//(otherMax & condition & head) => lit
				maxlits.push_back(lit);
				//Only a conflict if the i'th conditoin is already true and derived lit is false
				bool conflict = value(_conditions[i]) == l_True && value(lit) == l_False;
				return addClause(maxlits, conflict);
			}
		}

		else { // _head is false
			Lit lit;
			bool notBeingZeroIsRelevant = false;

			if (value(_conditions[i]) == l_False) {
				if (min >= bound) {
					auto lits = varsContributingToMin(i);
					lits.push_back(_head);
					lits.push_back(_conditions[i]);
					return addClause(lits, true);
				} else {
					continue;
				}
			}
			//In this case we can do more precise reasoning on the bound:
			//calculate min of aggregate without this variable
			//exclude all values of this var that do not succeed in making this small enough
			// We know: w_i*v_i < (b-minWithout(i))
			if (weight > 0) {
				// var =< BOT((bound - minWithout)/weight)
				auto val = (bound - minWithoutThisVar) / (double) weight;
				if (val == floor(val)) {
					val--;
				} else {
					val = floor(val);
				}
				lit = var->getLEQLit(val);
				notBeingZeroIsRelevant = (val < 0);
			} else {
				// var >= TOP((bound - minWithoutThisVar)/weight+0.01)
				auto val = (bound - minWithoutThisVar) / (double) weight;
				if (val == ceil(val)) {
					val++;
				} else {
					val = ceil(val);
				}
				lit = var->getGEQLit(val);
				notBeingZeroIsRelevant = (val > 0);
			}

			if (value(_conditions[i]) != l_True && notBeingZeroIsRelevant) {
				litlist minlits = varsContributingToMin(i);
				minlits.push_back(_head);
				//(otherMin & not head) => _condition
				minlits.push_back(_conditions[i]);
				auto cl = addClause(minlits, value(_conditions[i]) == l_False);
				if (cl != nullPtrClause) {
					return cl;
				}
			}
			//We can only propagate something about the value of term i if its condition is true (or propagated to be true)
			bool propagateValue = notBeingZeroIsRelevant || value(_conditions[i]) == l_True;
			if (propagateValue && value(lit) != l_True) {
				litlist minlits = varsContributingToMin(i);
				minlits.push_back(_head);
				minlits.push_back(not _conditions[i]);
				//(otherMin & conditions & not head) => lit
				minlits.push_back(lit);
				//Only a conflict if the i'th conditoin is already true and derived lit is false
				bool conflict = (value(_conditions[i]) == l_True) && (value(lit) == l_False);
				return addClause(minlits, conflict);
			}
		}
	}
	return nullPtrClause;
}

/*
 * PRODUCTS
 */
void FDProdConstraint::setWeights(const std::vector<Weight>& w) {
	MAssert(w.size() == 1);
	_weight = w[0];
}

void FDProdConstraint::initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel,
		IntView* bound) {
	if (weight == 0) {
		new FDSumConstraint(getID(), &getPCSolver(), head, conditions, { bound }, { 1 }, invertEqType(rel), weight);
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

	sharedInitialization(head, conditions, set, { weight }, rel, bound);
}

FDProdConstraint::FDProdConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const Weight& weight, EqType rel, const Weight& bound)
		: FDAggConstraint(id, engine, "fdprodconstr") {
	initialize(head, conditions, set, weight, rel, createBound(bound, bound));
}

FDProdConstraint::FDProdConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const Weight& weight, EqType rel, IntView* bound)
		: FDAggConstraint(id, engine, "fdprodconstr") {
	initialize(head, conditions, set, weight, rel, bound);
}

/**
 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
 * But excludes the excludedVar'th variable
 */
litlist FDProdConstraint::varsContributingToMax(size_t excludedVar) const {
	return varsContributingToMax(excludedVar, true);
}
litlist FDProdConstraint::varsContributingToMin(size_t excludedVar) const {
	return varsContributingToMax(excludedVar, true);
}
litlist FDProdConstraint::varsContributingToAbsVal() const {
	return varsContributingToAbsVal(_vars.size());
}

litlist FDProdConstraint::varsContributingToAbsVal(size_t excludedVar) const {
	litlist lits;
	//TODO: In case one of the variable is equal to zero, better explanation can be made
	for (uint i = 0; i < _vars.size(); ++i) {
		if (i == excludedVar) {
			continue;
		}
		if (value(_conditions[i]) == l_False) {
			lits.push_back(_conditions[i]);
			continue;
		}
		if (value(_conditions[i]) == l_True) {
			lits.push_back(not _conditions[i]);
		}
		lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
		lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
	}
	return lits;
}

litlist FDProdConstraint::varsContributingToMax(size_t excludedVar, bool canBeNegative) const {
	if (canBeNegative) {
		return varsContributingToAbsVal(excludedVar);
	}
	//TODO: In case one of the variable is equal to zero, better explanation can be made
	litlist lits;
	for (uint i = 0; i < _vars.size(); ++i) {
		if (i == excludedVar) {
			continue;
		}
		if (value(_conditions[i]) == l_False) {
			lits.push_back(_conditions[i]);
			continue;
		}
		if (value(_conditions[i]) == l_True) {
			lits.push_back(not _conditions[i]);
		}
		if (_weight >= 0) {
			lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
		} else {
			lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
		}
	}
	return lits;

}
litlist FDProdConstraint::varsContributingToMin(size_t excludedVar, bool canBeNegative) const {
	if (canBeNegative) {
		return varsContributingToAbsVal(excludedVar);
	}
	//TODO: In case one of the variable is equal to zero, better explanation can be made

	litlist lits;
	for (uint i = 0; i < _vars.size(); ++i) {
		if (i == excludedVar) {
			continue;
		}
		if (value(_conditions[i]) == l_False) {
			lits.push_back(_conditions[i]);
			continue;
		}
		if (value(_conditions[i]) == l_True) {
			lits.push_back(not _conditions[i]);
		}
		if (_weight < 0) {
			lits.push_back(not _vars[i]->getLEQLit(_vars[i]->maxValue()));
		} else {
			lits.push_back(not _vars[i]->getGEQLit(_vars[i]->minValue()));
		}
	}
	return lits;
}

//NOTE: for products, this does not include the weight!!! and also... This is an estimate.
// varloc might not exist!
std::pair<int, int> FDProdConstraint::getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const {
	if (canContainNegatives()) {
		int absmax = 1;
		int decidedval = 1;
		bool decided = true;
		for (uint i = 0; i < _vars.size(); ++i) {
			if (i == excludedVar) {
				continue;
			}
			if (value(_conditions[i]) == l_False) {
				continue;
			}
			auto minval = _vars[i]->minValue();
			auto maxval = _vars[i]->maxValue();
			if (value(_conditions[i]) != l_True) {
				minval = minval < 1 ? minval : 1;
				maxval = maxval > 1 ? maxval : 1;
			}
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
			if (i != excludedVar && value(_conditions[i]) != l_False) {
				auto minval = _vars[i]->minValue();
				auto maxval = _vars[i]->maxValue();
				min *= minval;
				max *= maxval;
			}
		}
		return {min,max};
	}
}

rClause FDProdConstraint::notifypropagate() {
	auto minmax = getMinAndMaxPossibleAggVals();
	int min = minmax.first;
	int max = minmax.second;
	int minbound = _bound->minValue();
	int maxbound = _bound->maxValue();
	bool boundKnown = (minbound == maxbound);

	if (min == max && boundKnown) {
		return check(min, minbound);
	}

	if (canContainNegatives()) {
		return notifypropagateWithNeg(min, max, minbound, maxbound);
	}
	return notifypropagateWithoutNeg(min, max, minbound, maxbound);
}

rClause FDProdConstraint::check(int val, int boundvalue) {
	auto headval = value(_head);
	litlist lits;
	bool conflict = false;
	if ((val * _weight) >= boundvalue) {
		if (headval == l_True) {
			return nullPtrClause;
		}
		lits = FDAggConstraint::varsContributingToMin();
		lits.push_back(_head);

		if (headval == l_False) {
			conflict = true;
		}
	} else {
		if (headval == l_False) {
			return nullPtrClause;
		}
		lits = FDAggConstraint::varsContributingToMax();
		lits.push_back(not _head);
		if (headval == l_True) {
			conflict = true;
		}
	}

	//We want to construct: current situation implies (head or not head, depending on previous context)
	auto extralit = not _bound->getLEQLit(boundvalue);
	MAssert(value(extralit)==l_False);
	lits.push_back(extralit);
	extralit = not _bound->getGEQLit(boundvalue);
	MAssert(value(extralit)==l_False);
	lits.push_back(extralit);

	return addClause(lits, conflict);
}

litlist FDProdConstraint::explainNotNegative() {
	litlist lits;
	for (uint i = 0; i < _vars.size(); ++i) {
		if (value(_conditions[i]) == l_False) {
			lits.push_back(not _conditions[i]);
		} else {
			lits.push_back(_vars[i]->getLEQLit(-1));
		}
	}
	return lits;
}

rClause FDProdConstraint::notifypropagateWithoutNeg(int mini, int maxi, int minbound, int maxbound) {
	auto headval = value(_head);

	MAssert(_weight != 0);
	//Constructor should guarantee this.

	int realmax = max(mini * _weight, maxi * _weight);
	int realmin = min(mini * _weight, maxi * _weight);
	bool reverted = (_weight < 0); //whether or not the min and max values have changed place

	//First propagation: Aggregate and bound -> head
	if (headval == l_Undef) {
		litlist lits = explainNotNegative();
		bool propagate = false;
		if (realmin >= maxbound) {
			propagate = true;
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
			//List all vars that have had a contribution to realmin
			for (uint i = 0; i < _vars.size(); ++i) {
				if (value(_conditions[i]) == l_False) {
					lits.push_back(_conditions[i]);
					continue;
				}
				if (value(_conditions[i]) == l_True) {
					lits.push_back(not _conditions[i]);
				}
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
				if (value(_conditions[i]) == l_False) {
					lits.push_back(_conditions[i]);
					continue;
				}
				if (value(_conditions[i]) == l_True) {
					lits.push_back(not _conditions[i]);
				}
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
			litlist lits = explainNotNegative();
			lits.push_back(not _head);
			//List all vars that have had a contribution to realmax
			for (auto maxlit : FDAggConstraint::varsContributingToMax()) {
				lits.push_back(maxlit);
			}
			auto boundlit = _bound->getLEQLit(realmax);
			lits.push_back(boundlit);
			bool conflict = value(boundlit) == l_False;
			return addClause(lits, conflict);
		}

		//PROPAGATION 2b: head and bound to agg
		//PROD{x_i} >= [minbound,maxbound], hence certainly Prod{x_i} >= minbound, we implemant realmax >=minbound
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			auto minval = var->minValue();
			auto maxval = var->maxValue();
			if (value(_conditions[i]) != l_True) {
				minval = minval < 1 ? minval : 1;
				maxval = maxval > 1 ? maxval : 1;
			}
			auto varusedval = reverted ? minval : maxval; //The value that has been used for var to calculate realmax
			if (value(_conditions[i]) == l_False) {
				varusedval = 1;
			}
			double maxWithoutThisVar;
			if (varusedval == 0) {
				MAssert(realmax == 0);
				auto minmaxnovar = getMinAndMaxPossibleAggValsWithout(i);
				maxWithoutThisVar = max(minmaxnovar.first * _weight, minmaxnovar.second * _weight);
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
			bool conditionRelevant = false;
			if (not reverted) {
				lit = var->getGEQLit(factormissing);
				conditionRelevant = factormissing > 1;
			} else {
				lit = var->getLEQLit(factormissing);
				conditionRelevant = factormissing < 1;
			}

			litlist lits = explainNotNegative();
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));
			//List all vars that have had a contribution to realmax
			for (auto maxlit : FDAggConstraint::varsContributingToMax()) {
				lits.push_back(maxlit);
			}

			if (value(_conditions[i]) != l_True && conditionRelevant) {
				litlist litscopy = litlist(lits);
				litscopy.push_back(_conditions[i]);
				bool conflict = value(_conditions[i]) == l_False;
				auto cl = addClause(litscopy, conflict);
				if (conflict) {
					return cl;
				}
			}

			bool propagateValue = value(_conditions[i]) == l_True || conditionRelevant;
			if (propagateValue && value(lit) != l_True) {
				lits.push_back(not _conditions[i]);
				lits.push_back(lit);
				bool conflict = value(_conditions[i]) == l_True && value(lit) == l_False;
				return addClause(lits, conflict);
			}
		}
	}
	//PROPAGATION 2: HEAD -> AGG AND BOUND
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
			litlist lits = explainNotNegative();
			lits.push_back(_head);
			//List all vars that have had a contribution to realmin
			for (auto minlit : FDAggConstraint::varsContributingToMin()) {
				lits.push_back(minlit);
			}
			auto boundlit = _bound->getGEQLit(realmin);
			lits.push_back(boundlit);
			return addClause(lits, value(boundlit) == l_False);
		}

		//PROPAGATION 2b: head and bound to agg
		//PROD{x_i} < [minbound,maxbound], hence certainly Prod{x_i} < maxbound, we implement realmin < maxbound
		for (uint i = 0; i < _vars.size(); ++i) {
			auto var = _vars[i];
			auto minval = var->minValue();
			auto maxval = var->maxValue();
			if (value(_conditions[i]) != l_True) {
				minval = minval < 1 ? minval : 1;
				maxval = maxval > 1 ? maxval : 1;
			}
			auto varusedval = reverted ? maxval : minval; //The value that has been used for var to calculate realmmin
			if (value(_conditions[i]) == l_False) {
				varusedval = 1;
			}
			double minWithoutThisVar;
			if (varusedval == 0) {
				MAssert(realmin == 0);
				auto minmaxnovar = getMinAndMaxPossibleAggValsWithout(i);
				minWithoutThisVar = min(minmaxnovar.first * _weight, minmaxnovar.second * _weight);
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
			bool conditionRelevant = false;
			if (reverted) {
				lit = var->getGEQLit(maxFactorThisVar);
				conditionRelevant = (maxFactorThisVar > 1);
			} else {
				lit = var->getLEQLit(maxFactorThisVar);
				conditionRelevant = (maxFactorThisVar < 1);
			}

			litlist lits = explainNotNegative();
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
			//List all vars that have had a contribution to realmin
			for (auto minlit : FDAggConstraint::varsContributingToMin()) {
				lits.push_back(minlit);
			}

			if (value(_conditions[i]) != l_True && conditionRelevant) {
				litlist litscopy = litlist(lits);
				litscopy.push_back(_conditions[i]);
				bool conflict = value(_conditions[i]) == l_False;
				auto cl = addClause(litscopy, conflict);
				if (conflict) {
					return cl;
				}
			}
			bool propagateValue = value(_conditions[i]) == l_True || conditionRelevant;
			if (propagateValue && value(lit) != l_True) {
				lits.push_back(not _conditions[i]);
				lits.push_back(lit);
				bool conflict = value(_conditions[i]) == l_True && value(lit) == l_False;
				return addClause(lits, conflict);
			}
		}
	}
	return nullPtrClause;
}

rClause FDProdConstraint::notifypropagateWithNeg(int minval, int maxval, int minbound, int maxbound) {
	auto headval = value(_head);

	int realmax = abs(max(minval * _weight, maxval * _weight));
	int realmin = -realmax;

	//PROPAGATION 1: from agg and bound to head
	if (headval == l_Undef) {
		litlist lits = varsContributingToAbsVal();
		if (realmin >= maxbound) {
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
			addClause(lits,false);
		} else if (realmax < minbound) {
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));
			addClause(lits,false);
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
			litlist lits = varsContributingToAbsVal();
			lits.push_back(not _head);
			auto boundlit = _bound->getLEQLit(realmax);
			lits.push_back(boundlit);
			addClause(lits, value(boundlit) == l_False);
		}
	} else if (headval == l_False) {
		//PROD < bound
		if (realmin > minbound) {
			litlist lits = varsContributingToAbsVal();
			lits.push_back(_head);
			auto boundlit = _bound->getGEQLit(realmin);
			lits.push_back(boundlit);
			addClause(lits, value(boundlit) == l_False);
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
			if (value(_conditions[i]) == l_False) {
				//TODO might be optimized: if value has no influence, maybe also propagtation is possible
				continue;
			}
			auto absvarmax = max(abs(var->maxValue()), abs(var->minValue()));
			if (absvarmax == 0) {
				//TODO Can be optimized: we will want to do a derivation towards _condition[i] here, probably should be false unless bound can be zero...
				continue;
			}
			auto maxWithoutThisVar = abs(realmax / absvarmax);
			if (maxWithoutThisVar == 0) {
				//TODO Can be optimized. Should be thought about...
				continue;
			}
			auto stillNeeded = ceil(abs(propagationbound / maxWithoutThisVar));

			bool propagate = false;
			bool conflict = false;
			litlist lits = varsContributingToAbsVal(i);

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
				addClause(lits, conflict);
			}
		}
	}
	return nullPtrClause;
}

