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

using namespace std;
using namespace MinisatID;

FDAggConstraint::FDAggConstraint(PCSolver* s, const std::string& name)
		: Propagator(s, name) {
}

IntView* FDAggConstraint::negation(IntView* bound) {
	auto result = createBound(-bound->maxValue(), -bound->minValue()); // Very inefficient if enum
	auto head = getPCSolver().newAtom();
	auto headIsTrue = mkPosLit(head);
	auto t = getPCSolver().getTrueLit();
	getPCSolver().setTrue(headIsTrue, this); //FIXME: explanation
	const int& zero = 0; //doing this here, to make the disambiguation.
	add(CPSumWeighted(headIsTrue, { t, t }, { bound->getID(), result->getID() }, { 1, 1 }, EqType::GEQ, zero));
	add(CPSumWeighted(headIsTrue, { t, t }, { bound->getID(), result->getID() }, { -1, -1 }, EqType::GEQ, zero));
	if (verbosity() > 5) {
		clog << toString(head) << " <=> var" << result->toString() << " + var" << bound->toString() << " = 0" << endl;
	}
	//We cannot use equality here, since that would cause loops...
	return result;
}

IntView* FDAggConstraint::createBound(const Weight& min, const Weight& max) {
	auto id = getPCSolver().newID();
	add(IntVarRange(id, min, max));
	return getPCSolver().getIntView(id, 0);
}

void FDAggConstraint::sharedInitialization(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, IntView* bound) {

	auto conditionswithpartial = conditions;
	for(uint i=0; i<conditions.size();++i){
		if(set[i]->isPartial()){
			auto condandnotpart = getPCSolver().newAtom();
			// TODO improve algorithm instead of doing this recoding that introduces an additiona tseitin?
			add(Implication(mkPosLit(condandnotpart), ImplicationType::EQUIVALENT, {conditions[i], not set[i]->getNoImageLit()}, true));
			conditionswithpartial[i] = mkPosLit(condandnotpart);
		}
	}

	//FIXME .. PASS THE ID
	if (set.size() == 0) {
		Weight neutral = 0;
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
		add(Implication(head, ImplicationType::EQUIVALENT, { condition }, true));
		if (verbosity() > 5) {
			clog << "Set was empty, FDAGGConstraint simplified to:";
			clog << toString(head) << " <=> " << toString(condition) << endl;
		}
		notifyNotPresent();
		return;
	}
	_head = head;
	_vars = set;
	if (rel == EqType::EQ || rel == EqType::NEQ) {
		auto eq = (rel == EqType::EQ);
		auto one = mkPosLit(getPCSolver().newAtom());
		auto two = mkPosLit(getPCSolver().newAtom());
		add(Implication(eq ? head : not head, ImplicationType::EQUIVALENT, { one, two }, true));
		if (verbosity() > 5) {
			clog << "split FDAggConstraint with head " << toString(head) << " into GEQ with head " << toString(one) << " and LEQ with head " << toString(two)
					<< endl;
			clog << toString(eq ? head : not head) << " <=> " << toString(one) << " && " << toString(two) << endl;
		}
		_head = one;
		if (getType() == AggType::PROD) {
			std::vector<VarID> varids;
			for(auto v: _vars){
				varids.push_back(v->getID());
			}
			add(CPProdWeighted(two, conditionswithpartial, varids, weights.front(), EqType::LEQ, bound->getID()));
		} else {
			MAssert(getType() == AggType::SUM);
			std::vector<VarID> varids;
			for(auto v: _vars){
				varids.push_back(v->getID());
			}
			varids.push_back(bound->getID());
			auto newweights = weights;
			newweights.push_back(Weight(-1));
			auto newconditions = conditionswithpartial;
			newconditions.push_back(getPCSolver().getTrueLit());
			add(CPSumWeighted(two, newconditions, varids, newweights, EqType::LEQ, Weight(0)));
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

	_conditions = conditionswithpartial;
}

void FDAggConstraint::watchRelevantVars() {
	if (not isPresent()) {
		//we only go watching vars if the initialisation did not allready decide taht this aggregate is useless.
		return;
	}

	getPCSolver().accept(this, _head, FAST);
	getPCSolver().accept(this, not _head, FAST);
	for (auto var : _vars) {
		getPCSolver().acceptBounds(var, this);
		if(var->isPartial()){
			getPCSolver().accept(this, var->getNoImageLit(), FAST);
			getPCSolver().accept(this, not var->getNoImageLit(), FAST);
		}
	}
	for (auto c : _conditions) {
		getPCSolver().accept(this, c, FAST);
		getPCSolver().accept(this, not c, FAST);
	}
	getPCSolver().acceptBounds(_bound, this);
	getPCSolver().acceptForPropagation(this);
	// TODO remove trivially true aggregates
}


#ifdef NOARBITPREC
bool additionOverflow(Weight x, Weight y) {
	if (((double) x) + y > getMaxElem<Weight>()) {
		return true;
	}
	if (((double) x) + y < getMinElem<Weight>()) {
		return true;
	}
	return false;
}
#else
bool additionOverflow(Weight, Weight) {
	return false;
}
#endif

/**
 * Adds the disjunction of lits to the solver and returns the clause
 */
rClause FDAggConstraint::addClause(litlist& lits, bool conflict) {
	auto c = getPCSolver().createClause(Disjunction(lits), true);
	//getPCSolver().printClause(c);
	if (conflict) { // Conflict
		getPCSolver().addConflictClause(c);
		return c;
	} else {
#ifdef DEBUG
		bool somenotfalse = false;
		for(auto lit:lits) {
			somenotfalse |= value(lit)!=l_False;
		}
		MAssert(somenotfalse);
#endif
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
			if (set[i]->getID() == newset[j]->getID()) {
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
		if ((*wi) == Weight(0) || getPCSolver().rootValue(*ci) == l_False) {
			si = newset.erase(si);
			wi = newweights.erase(wi);
			ci = newConditions.erase(ci);
		} else {
			++si;
			++wi;
			++ci;
		}
	}

#ifdef NOARBITPREC
	double absmax(0);
	for (uint i = 0; i < newset.size(); ++i) {
		double sumterm = newweights[i];
		double miv = newset[i]->minValue(); // IMPORTANT: first cast to double (otherwise abs is wrong!)
		double mav = newset[i]->maxValue(); // IMPORTANT: first cast to double (otherwise abs is wrong!)
		double maxterm = abs(sumterm)*max(abs(mav), abs(miv));
		absmax += maxterm;
	}
	if(absmax>=getMaxElem<Weight>()){
		throw idpexception("Overflow possible for sum of a set of variables in limited integer precision. Compile with GMP to resolve overflow issues.");
	}
#endif
	sharedInitialization(head, newConditions, newset, newweights, rel, bound);
	watchRelevantVars();

	vector<int> index(_vars.size(), 0);
	for (uint i = 0 ; i != index.size() ; i++) {
	    index[i] = i;
	}
	sort(index.begin(), index.end(),
	    [&](const int& a, const int& b) {
	        return (abs(_vars[a]->maxValue()-_vars[a]->minValue()) > abs(_vars[b]->maxValue()-_vars[b]->minValue()));
	    }
	);
	auto v=_vars; auto w=_weights; auto c=_conditions;
	for(uint i=0; i<index.size(); ++i){
		_vars[i]=v[index[i]];
		_weights[i]=w[index[i]];
		_conditions[i]=c[index[i]];
	}
}

FDSumConstraint::FDSumConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, const Weight& bound)
		: FDAggConstraint(engine, "fdsumconstr") {
	MAssert(weights.size() == set.size());
	MAssert(conditions.size() == set.size());
	initialize(head, conditions, set, weights, rel, createBound(bound, bound));
}

FDSumConstraint::FDSumConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const std::vector<Weight>& weights, EqType rel, IntView* bound)
		: FDAggConstraint(engine, "fdsumconstr") {
	MAssert(weights.size() == set.size());
	MAssert(conditions.size() == set.size());
	MAssert(bound->minValue() == bound->maxValue());
	initialize(head, conditions, set, weights, rel, bound);
}

std::pair<Weight, Weight> FDSumConstraint::getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const {
	Weight min = 0, max = 0;
	//clog <<"Set\n";
	for (uint i = 0; i < _vars.size(); ++i) {
		//clog <<"\t" <<_vars[i]->toString() <<"[" <<_vars[i]->minValue() <<".." <<_vars[i]->maxValue() <<"]*" <<_weights[i] <<" if " <<toString(_conditions[i]) <<"\n";
		if (i == excludedVar) {
			//Variable has no influence as he should be excluded
			continue;
		}
		auto condval = value(_conditions[i]);
		if (condval == l_False) {
			//Variable has no influence as his conditions is false
			continue;
		}

		auto weight = _weights[i];
		auto minval = _vars[i]->minValue();
		auto maxval = _vars[i]->maxValue();
		if (condval != l_True) {
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
	//clog <<"\n";
	return {min,max};
}

// TODO print code:
/*cerr <<toString(_head) <<" <=> ";
for(uint i = 0; i<_vars.size(); ++i){
	cerr <<_weights[i] <<"*" <<_vars[i]->toString() <<"[" <<_vars[i]->minValue() <<"," <<_vars[i]->maxValue() <<"|" <<_vars[i]->origMinValue() <<"," <<_vars[i]->origMaxValue() <<"]" << " if " <<toString(_conditions[i]) <<" + ";
}
cerr <<" >= " <<getBound() <<"\n";*/

/**
 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
 * But excludes the excludedVar'th variable
 *
 * The returned list only contains literals CURRENTLY FALSE!
 *
 * Return lits such that absmax + sum of max-origmax values < bound
 */
litlist FDSumConstraint::varsContributingToMax(size_t excludedVar, Weight bound) const {
	litlist lits;
	stringstream ss;
	for (uint j = 0; j < _vars.size(); ++j) {
		if (j == excludedVar) {
			continue;
		}
		auto condval = value(_conditions[j]);
		if (condval == l_False) {
			if (_weights[j] <= 0 && _vars[j]->origMinValue() >= 0) { // neg value
				continue;
			}
			if (_weights[j] > 0 && _vars[j]->origMaxValue() <= 0) { // neg value
				continue;
			}
			lits.push_back(_conditions[j]);
		} else {
			if (condval == l_True) {
				lits.push_back(not _conditions[j]);
			}
			if (_weights[j] < 0) {
				lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
			} else {
				lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
			}
		}
	}
#ifdef DEBUG
	bool sometrue = false;
	for(auto lit:lits) {
		sometrue |= value(lit)!=l_False;
	}
	MAssert(not sometrue);
#endif
	return lits;
}
/*
 * The returned list only contains literals CURRENTLY FALSE!
 *
 * Return lits such that absmin + sum of min-origmin values >= bound
 */
litlist FDSumConstraint::varsContributingToMin(size_t excludedVar, Weight bound) const {
	litlist lits;
	for (uint j = 0; j < _vars.size(); ++j) {
		if (j == excludedVar) {
			continue;
		}
		auto condval = value(_conditions[j]);
		if (condval == l_False) {
			if (_weights[j] > 0 && _vars[j]->origMinValue() >= 0) {
				continue;
			}
			if (_weights[j] <= 0 && _vars[j]->origMaxValue() <= 0) {
				continue;
			}
			lits.push_back(_conditions[j]);
		} else {
			if (condval == l_True) {
				lits.push_back(not _conditions[j]);
			}
			if (_weights[j] < 0) {
				lits.push_back(not _vars[j]->getLEQLit(_vars[j]->maxValue()));
			} else {
				lits.push_back(not _vars[j]->getGEQLit(_vars[j]->minValue()));
			}
		}
	}
#ifdef DEBUG
	bool sometrue = false;
	for(auto lit:lits) {
		sometrue |= value(lit)!=l_False;
	}
	MAssert(not sometrue);
#endif
	return lits;
}

rClause FDSumConstraint::createClause(Contrib use, bool conflict, const std::vector<Lit>& extralits, Weight bound) {
	/*	auto someunknown = false;
	 for(auto lit: extralits){
	 if(value(lit)==l_Undef){
	 someunknown = true;
	 }
	 }
	 if(not conflict && not someunknown){
	 return nullPtrClause;
	 }*/
	if (use == Contrib::MIN) {
		auto minlits = varsContributingToMin(bound);
		for (auto lit : extralits) {
			minlits.push_back(lit);
		}
		return addClause(minlits, conflict);
	} else {
		auto maxlits = varsContributingToMax(bound);
		for (auto lit : extralits) {
			maxlits.push_back(lit);
		}
		return addClause(maxlits, conflict);
	}
}
rClause FDSumConstraint::createClauseExcl(Contrib use, size_t varindex, bool conflict, const std::vector<Lit>& extralits, Weight bound) {
	/*	auto someunknown = false;
	 for(auto lit: extralits){
	 if(value(lit)==l_Undef){
	 someunknown = true;
	 }
	 }
	 if(not conflict && not someunknown){
	 return nullPtrClause;
	 }*/
	if (use == Contrib::MIN) {
		auto minlits = varsContributingToMin(varindex, bound);
		for (auto lit : extralits) {
			minlits.push_back(lit);
		}
		return addClause(minlits, conflict);
	} else {
		auto maxlits = varsContributingToMax(varindex, bound);
		for (auto lit : extralits) {
			maxlits.push_back(lit);
		}
		return addClause(maxlits, conflict);
	}
}

#define conflCheck(c) \
		auto cl = c; \
		if (cl != nullPtrClause) { \
			return cl; \
		}\


rClause FDSumConstraint::notifypropagate() {
	auto _headval = value(_head);
	auto minmax = getMinAndMaxPossibleAggVals();
	auto min = minmax.first;
	auto max = minmax.second;

	auto bound = getBound();

	//Propagation AGG =>  head
	if (_headval == l_Undef) {
		if (min >= bound) {
			conflCheck(createClause(Contrib::MIN, false, {_head}, bound)); // Enough such that sum of min values >= bound
			// Note: no conflict as head is unknown
		} else if (max < bound) {
			conflCheck(createClause(Contrib::MAX, false, {not _head}, bound)); // Enough such that sum of max values < bound
			// Note: no conflict as head is unknown
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

		if (value(_conditions[i]) == l_False) { //In this case, we can only derive a possible conflict.
			if (_headval == l_True && max < bound) {
				conflCheck(createClauseExcl(Contrib::MAX, i, true, {not _head, _conditions[i]}, bound)); // Enough such that sum of max values without i < bound
			} else if (_headval == l_False && min >= bound) {
				conflCheck(createClauseExcl(Contrib::MIN, i, true, {_head, _conditions[i]}, bound)); // Enough such that sum of min values without i >= bound
			}
			continue;
		}
		MAssert(value(_conditions[i])!=l_False);

		// Compute max and min without this var more efficiently than going over all vars again
		auto maxWithoutThisVar = max, minWithoutThisVar = min;
		auto minval = var->minValue(), maxval = var->maxValue();
		if (value(_conditions[i]) != l_True) {
		// condition i is possibly false
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

		// In these cases, more precise bounds reasoning is possible:
		// If excluding the value of the variable from the minimum/maximum, would it violate the bound?
		Lit lit;
		bool notBeingZeroIsRelevant = false;
		if (_headval == l_True) {
			// We know: w_i*v_i >= (b-minWithout(i))
			Weight maxIfConditionIsTrue = 0;
			if (weight > 0) {
				auto val = ceildiv((bound - maxWithoutThisVar), weight);
				lit = var->getGEQLit(val);
				notBeingZeroIsRelevant = (val > 0);
				maxIfConditionIsTrue = maxWithoutThisVar + (var->maxValue() * weight);
			} else {
				auto val = floordiv((bound - maxWithoutThisVar), weight);
				lit = var->getLEQLit(val);
				notBeingZeroIsRelevant = (val < 0);
				maxIfConditionIsTrue = maxWithoutThisVar + (var->minValue() * weight);
			}

			if (maxIfConditionIsTrue < bound && value(_conditions[i]) != l_False) {
				conflCheck(createClauseExcl(Contrib::MAX, i, value(_conditions[i]) == l_True, {lit, not _head, not _conditions[i]}, bound - var->maxValue()));
				continue; // enough such that sum of max values without i < bound - max value i
			}
			if (value(_conditions[i]) == l_Undef && notBeingZeroIsRelevant) { // Never conflict (condition is unknown)
				conflCheck(createClauseExcl(Contrib::MAX, i, false, {not _head, _conditions[i]}, bound));
					// enough such that sum of max values without i < bound
			}
			//We can only propagate something about the value of term i if its condition is true (or propagated to be true)
			auto propagateValue = notBeingZeroIsRelevant || value(_conditions[i]) == l_True;
			if (propagateValue && value(lit) != l_True) { //Some values not yet excluded
				conflCheck(createClauseExcl(Contrib::MAX, i, value(_conditions[i]) == l_True && value(lit) == l_False, {not _head, not _conditions[i], lit}, bound));
					// enough such that sum of max values without i < bound
			}
		} else { // _head is false
			// We know: w_i*v_i < (b-minWithout(i))
			Weight minIfConditionIsTrue = 0;
			if (weight > 0) {
				auto val = floordiv(bound - minWithoutThisVar, weight);
				if (weight*val == bound - minWithoutThisVar) {
					val-=1;
				}
				lit = var->getLEQLit(val);
				notBeingZeroIsRelevant = (val < 0);
				minIfConditionIsTrue = minWithoutThisVar + (var->minValue() * weight);
			} else {
				auto val = ceildiv(bound - minWithoutThisVar, weight);
				if (val*weight == bound - minWithoutThisVar) {
					val+=1;
				}
				lit = var->getGEQLit(val);
				notBeingZeroIsRelevant = (val > 0);
				minIfConditionIsTrue = minWithoutThisVar + (var->maxValue() * weight);
			}

			if (minIfConditionIsTrue > bound && value(_conditions[i]) != l_False) {
				conflCheck(createClauseExcl(Contrib::MIN, i, value(_conditions[i]) == l_True, {lit, _head, not _conditions[i]}, bound-var->minValue()));
				// enough such that sum of min values without i >= bound - min value i
				continue;
			}
			if (value(_conditions[i]) == l_Undef && notBeingZeroIsRelevant) { // Never conflict (condition is unknown)
				conflCheck(createClauseExcl(Contrib::MIN, i, false, {_head, _conditions[i]}, bound));
				// enough such that sum of max values without i =< bound
			}
			//We can only propagate something about the value of term i if its condition is true (or propagated to be true)
			auto propagateValue = notBeingZeroIsRelevant || value(_conditions[i]) == l_True;
			if (propagateValue && value(lit) != l_True) {
				conflCheck(createClauseExcl(Contrib::MIN, i, value(_conditions[i]) == l_True && value(lit)==l_False, {_head, not _conditions[i], lit}, bound));
				// enough such that sum of max values without i =< bound
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

bool FDProdConstraint::canContainNegatives() const {
	return value(_definitelyPositive) != l_True;
}

void FDProdConstraint::initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel,
		IntView* bound) {
	std::vector<IntView*> newset;
	std::vector<Lit> newconditions;
	Weight newweight(weight);
	for (uint i = 0; i < set.size(); ++i) {
		if (getPCSolver().rootValue(conditions[i]) == l_False) {
			//Irrelevant for this aggregate
			continue;
		}
		if (getPCSolver().rootValue(conditions[i]) == l_True && (set[i]->origMinValue() == set[i]->origMaxValue())) {
			//value of this term is known, hence we can include it in the weight
			newweight *= set[i]->origMinValue();
			continue;
		}
		if (getPCSolver().rootValue(conditions[i]) == l_True && (set[i]->origMinValue() < 0) && (set[i]->origMaxValue() <= 0)) {
			//Variable is guaranteed to be negative. Can be optimised by including "-1" in the weight and keeping monotonicity of product
			//Can only be done in case this variable is known to be certainly in the set.
			auto varid = getPCSolver().newID();
			add(IntVarRange(varid, -set[i]->origMaxValue(), -set[i]->origMinValue()));
			auto truelit = getPCSolver().getTrueLit();
			add(CPSumWeighted(truelit, { truelit, truelit }, { set[i]->getID(), varid }, { Weight(1), Weight(1) }, EqType::EQ, Weight(0)));
			newweight *= -1;
			newset.push_back(getPCSolver().getIntView(varid, Weight(0)));
			newconditions.push_back(conditions[i]);
			continue;
		}

		newset.push_back(set[i]);
		newconditions.push_back(conditions[i]);

	}

	if (newweight == 0) {
		add(CPBinaryRel(head, bound->getID(), invertEqType(rel), 0));
		notifyNotPresent();
		return;
	}

	if(newset.size() == 1 && getPCSolver().rootValue(newconditions[0])==l_True){
		//Transform _head <=> PROD set[0]  >= _bound to
		//set[0] - bound >= 0
		add(CPSumWeighted(head, {newconditions[0],getPCSolver().getTrueLit()}, {newset[0]->getID(),bound->getID()}, {newweight, -1}, rel,  0));
		notifyNotPresent();
		return;
	}

#ifdef NOARBITPREC
	double absmax(abs(newweight)); //note that s == 0 unless set
	for (auto var : newset) {
		double miv = var->minValue(); // IMPORTANT: first cast to double (otherwise abs is wrong!)
		double mav = var->maxValue(); // IMPORTANT: first cast to double (otherwise abs is wrong!)
		absmax *= max(abs(miv), abs(mav));
	}
	if(absmax>=getMaxElem<Weight>()){
		throw idpexception("Overflow possible for product of a set of variables in limited integer precision. Compile with GMP to resolve overflow issues.");
	}
#endif

	sharedInitialization(head, newconditions, newset, { newweight }, rel, bound);
	if (not isPresent()) {
		return;
	}
	//For every variable, add a lit that says whether or not it is guaranteed to have postive influence on the set.
	std::vector<Lit> poslits;
	for (uint i = 0; i < _vars.size(); i++) {
		if (_vars[i]->origMinValue() < 0) {
			auto poslit = mkPosLit(getPCSolver().newAtom());
			auto notpresent = !_conditions[i];
			auto positive = _vars[i]->getGEQLit(0);
			add(Implication(poslit, ImplicationType::EQUIVALENT, { notpresent, positive }, false));
			poslits.push_back(poslit);
		}
	}
	if (poslits.size() == 0) {
		_definitelyPositive = getPCSolver().getTrueLit();
	} else if (poslits.size() == 1) {
		_definitelyPositive = poslits[0];
	} else {
		_definitelyPositive = mkPosLit(getPCSolver().newAtom());
		add(Implication(_definitelyPositive, ImplicationType::EQUIVALENT, poslits, true));
	}
	watchRelevantVars();

}

FDProdConstraint::FDProdConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const Weight& weight, EqType rel, const Weight& bound)
		: FDAggConstraint(engine, "fdprodconstr") {
	initialize(head, conditions, set, weight, rel, createBound(bound, bound));
}

FDProdConstraint::FDProdConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
		const Weight& weight, EqType rel, IntView* bound)
		: FDAggConstraint(engine, "fdprodconstr") {
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
	return varsContributingToMin(excludedVar, true);
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
std::pair<Weight, Weight> FDProdConstraint::getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const {
	if (canContainNegatives()) {
		Weight absmax = 1;
		Weight decidedval = 1;
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
		Weight min = 1, max = 1;
		for (uint i = 0; i < _vars.size(); ++i) {
			if (i != excludedVar && value(_conditions[i]) != l_False) {
				auto minval = _vars[i]->minValue();
				auto maxval = _vars[i]->maxValue();
				if (value(_conditions[i]) != l_True) {
					minval = minval < 1 ? minval : 1;
					maxval = maxval > 1 ? maxval : 1;
				}
				min *= minval;
				max *= maxval;
			}
		}
		return {min,max};
	}
}

rClause FDProdConstraint::notifypropagate() {
	auto minmax = getMinAndMaxPossibleAggVals();
	Weight min = minmax.first;
	Weight max = minmax.second;
	Weight minbound = _bound->minValue();
	Weight maxbound = _bound->maxValue();
	bool boundKnown = (minbound == maxbound);

	if (min == max && boundKnown) {
		return check(min, minbound);
	}
	if (canContainNegatives()) {
		return notifypropagateWithNeg(min, max, minbound, maxbound);
	}
	return notifypropagateWithoutNeg(min, max, minbound, maxbound);
}

rClause FDProdConstraint::check(Weight val, Weight boundvalue) {
	auto headval = value(_head);
	litlist lits;
	bool conflict = false;
	if ((val * _weight) >= boundvalue) {
		if (headval == l_True) {
			return nullPtrClause;
		}
		lits = varsContributingToMin();
		lits.push_back(_head);

		if (headval == l_False) {
			conflict = true;
		}
	} else {
		if (headval == l_False) {
			return nullPtrClause;
		}
		lits = varsContributingToMax();
		lits.push_back(not _head);
		if (headval == l_True) {
			conflict = true;
		}
	}

	//We want to construct: current situation implies (head or not head, depending on previous context)
	auto extralit = not _bound->getLEQLit(boundvalue);
	MAssert(value(extralit) == l_False);
	lits.push_back(extralit);
	extralit = not _bound->getGEQLit(boundvalue);
	MAssert(value(extralit) == l_False);
	lits.push_back(extralit);

	return addClause(lits, conflict);
}

rClause FDProdConstraint::notifypropagateWithoutNeg(Weight mini, Weight maxi, Weight minbound, Weight maxbound) {
	auto headval = value(_head);
	MAssert(not canContainNegatives());
	MAssert(value(_definitelyPositive) == l_True);
	//In EVERY LEARNED CLAUSE: Don't forget to add !_definitelyPositive!!!!!
	MAssert(_weight != 0);
	//Constructor should guarantee this.

	Weight realmax = max(mini * _weight, maxi * _weight);
	Weight realmin = min(mini * _weight, maxi * _weight);
	bool reverted = (_weight < 0); //whether or not the min and max values have changed place

	//First propagation: Aggregate and bound -> head
	if (headval == l_Undef) {

		litlist lits;
		bool propagate = false;
		if (realmin >= maxbound) {
			lits = varsContributingToMin();
			propagate = true;
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
			//List all vars that have had a contribution to realmin
		} else if (realmax < minbound) {
			lits = varsContributingToMax();
			propagate = true;
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));
		}
		if (propagate) {
			lits.push_back(!_definitelyPositive);
			auto c = getPCSolver().createClause(Disjunction(lits), true);
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
			//List all vars that have had a contribution to realmax
			litlist lits = varsContributingToMax();
			lits.push_back(!_definitelyPositive);
			lits.push_back(not _head);
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
			Weight maxWithoutThisVar;
			if (varusedval == 0) {
				MAssert(realmax == 0);
				auto minmaxnovar = getMinAndMaxPossibleAggValsWithout(i);
				maxWithoutThisVar = max(minmaxnovar.first * _weight, minmaxnovar.second * _weight);
			}else{
				maxWithoutThisVar = realmax / varusedval;
			}
			if (maxWithoutThisVar == 0) {
				//no propagation, this var cannot change anything.
				continue;
			}

			Weight factormissing;
			if (not reverted) {
				factormissing = ceildiv(minbound, maxWithoutThisVar);
			} else {
				factormissing = floordiv(minbound, maxWithoutThisVar);
			}
			Lit lit;
			bool conditionRelevant = false;
			bool beingNotInSetIsRelevant = false;
			if (value(_conditions[i]) != l_False) {
				auto maxIfConditionIsTrue = maxWithoutThisVar * (reverted ? var->minValue() : var->maxValue());
				beingNotInSetIsRelevant = (maxIfConditionIsTrue < minbound);
			}

			if (not reverted) {
				lit = var->getGEQLit(factormissing);
				conditionRelevant = factormissing > 1;
			} else {
				lit = var->getLEQLit(factormissing);
				conditionRelevant = factormissing < 1;
			}

			//List all vars that have had a contribution to realmax
			litlist lits = varsContributingToMax();
			lits.push_back(!_definitelyPositive);
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));

			if (beingNotInSetIsRelevant) {
				lits.push_back(not _conditions[i]);
				bool conflict = value(_conditions[i]) == l_True;
				return addClause(lits, conflict);
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
			//List all vars that have had a contribution to realmin
			litlist lits = varsContributingToMin();
			lits.push_back(!_definitelyPositive);
			lits.push_back(_head);
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
			auto varusedval = reverted ? maxval : minval; //The value that has been used for var to calculate realmin
			if (value(_conditions[i]) == l_False) {
				varusedval = 1;
			}
			Weight minWithoutThisVar;
			if (varusedval == 0) {
				MAssert(realmin == 0);
				auto minmaxnovar = getMinAndMaxPossibleAggValsWithout(i);
				minWithoutThisVar = min(minmaxnovar.first * _weight, minmaxnovar.second * _weight);
			} else {
				minWithoutThisVar = realmin / varusedval; // TODO can this be not an integer?
			}
			if (minWithoutThisVar == 0) {
				//no propagation, this var cannot change anything.
				continue;
			}
			Weight maxFactorThisVar(0);
			if (not reverted) {
				maxFactorThisVar = floordiv(maxbound, minWithoutThisVar);
				if (maxFactorThisVar*minWithoutThisVar == maxbound) {
					maxFactorThisVar-=1; //Because we can only get LEQlit
				}
			} else {
				maxFactorThisVar = ceildiv(maxbound, minWithoutThisVar);
				if (maxFactorThisVar*minWithoutThisVar == maxbound) {
					maxFactorThisVar+=1; //Because we can only get GEQlit
				}
			}
			bool beingNotInSetIsRelevant = false;
			if (value(_conditions[i]) != l_False) {
				auto minIfConditionIsTrue = minWithoutThisVar * (reverted ? var->maxValue() : var->minValue());
				beingNotInSetIsRelevant = (minIfConditionIsTrue >= maxbound);
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
			//List all vars that have had a contribution to realmin
			litlist lits = varsContributingToMin();
			lits.push_back(!_definitelyPositive);
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));

			if (beingNotInSetIsRelevant) {
				lits.push_back(not _conditions[i]);
				bool conflict = value(_conditions[i]) == l_True;
				return addClause(lits, conflict);
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

rClause FDProdConstraint::notifypropagateWithNeg(Weight minval, Weight maxval, Weight minbound, Weight maxbound) {
	auto headval = value(_head);

	Weight realmax = abs(max(minval * _weight, maxval * _weight));
	Weight realmin = -realmax;

	//PROPAGATION 1: from agg and bound to head
	if (headval == l_Undef) {
		litlist lits = varsContributingToAbsVal();
		if (realmin >= maxbound) {
			lits.push_back(_head);
			lits.push_back(not _bound->getLEQLit(maxbound));
			addClause(lits, false);
		} else if (realmax < minbound) {
			lits.push_back(not _head);
			lits.push_back(not _bound->getGEQLit(minbound));
			addClause(lits, false);
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
			bool conflict = value(boundlit) == l_False;
			auto c = addClause(lits, conflict);
			if(conflict){
				return c;
			}
		}
	} else if (headval == l_False) {
		//PROD < bound
		if (realmin > minbound) {
			litlist lits = varsContributingToAbsVal();
			lits.push_back(_head);
			auto boundlit = _bound->getGEQLit(realmin);
			lits.push_back(boundlit);
			bool conflict = value(boundlit) == l_False;
			auto c = addClause(lits, conflict);
			if(conflict){
				return c;
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
		propagationbound = (Weight(-1) * maxbound) + Weight(1);
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
			if (realmax==0) {
				//TODO Can be optimized. Should be thought about...
				continue;
			}
			auto stillNeeded = abs(ceildiv(propagationbound, realmax * absvarmax)); // TODO moved abs out of ceil, is this correct???

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
				auto c = addClause(lits, conflict);
				if(conflict){
					return c;
				}
			}
		}
	}
	return nullPtrClause;
}

