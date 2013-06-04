#pragma once

#include <vector>
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

// NOTE: always GEQ at the moment!
// 		_head <=> AGG >= _bound
class FDAggConstraint: public Propagator {
protected:
	Lit _head;
	std::vector<IntView*> _vars;
	IntView* _bound;
	std::vector<Lit> _conditions;

protected:
	FDAggConstraint(uint id, PCSolver* s, const std::string& name);
	virtual void setWeights(const std::vector<Weight>&) = 0;
	void sharedInitialization(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights,
			EqType rel, IntView* bound);

public:

	// Propagator methods
	virtual int getNbOfFormulas() const {
		return 1;
	}

	virtual void finishParsing(bool&) {
	}

	virtual void accept(ConstraintVisitor&) {
		// TODO not yet implemented
	}
	virtual rClause getExplanation(const Lit&) {
		throw idpexception("Invalid code path.");
	}
	virtual void notifyNewDecisionLevel() {
		throw idpexception("Invalid code path.");
	}
	virtual void notifyBacktrack(int, const Lit&) {
		throw idpexception("Invalid code path.");
	}
protected:

	/**
	 * Returns a pair (min,max), where the first of the two is an underbound on the values the aggregate can take
	 * and the second is an upperbound. These bounds are not exact. I.e. in some cases it is possible that the bounds
	 * can not be achieved. However, if the aggregates value can be decided, it is guaranteed that this method returns
	 * a pair where both values are equal.
	 */
	std::pair<int, int> getMinAndMaxPossibleAggVals() const;

	/**
	 * Similar to getMinAndMaxPossibleAggVals(), but without taking the excludedVar'th var into account.
	 * Hence returns a lower and upperbound of the aggregate with one variable excluded.
	 * If excludedVar is not in the range [0.._vars.size()[, returns a lower and upper bound for the entire aggregate
	 */
	virtual std::pair<int, int> getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const = 0;

	/**
	 * Returns a list of all variables contributing to the current maximum/minimum
	 */
	litlist varsContributingToMax() const;
	litlist varsContributingToMin() const;

	/**
	 * Returns a list of all variables contributing to the current maximum/minimum
	 * But excludes the excludedVar'th variable
	 */
	virtual litlist varsContributingToMax(size_t excludedVar) const = 0;
	virtual litlist varsContributingToMin(size_t excludedVar) const = 0;

	/**
	 * This method returns true if and only if one of the variables can still take negative values
	 */
	bool canContainNegatives() const;

	/**
	 * Returns the unary negation of this bound (-bound)
	 */
	IntView* negation(IntView* bound);

	/**
	 * Creates an intview which can only take the value of bound.
	 */
	IntView* createBound(const Weight& min, const Weight& max);

	/**
	 * Adds the disjunction of lits to the solver and returns the clause
	 * If criticalLit is false, this is a conflict-clause
	 * otherwise, a learned clause
	 */
	rClause addClause(litlist& lits, bool conflict);

	virtual AggType getType() const = 0;
};

class FDSumConstraint: public FDAggConstraint {
private:
	std::vector<Weight> _weights;
	void initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
			IntView* bound);

public:
	// Sum constraint: one weight for each var, where bound is an int.
	FDSumConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
			const std::vector<Weight>& weights, EqType rel, const int& bound);

	// Sum constraint: one weight for each var, where bound is an intview.
	FDSumConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set,
			const std::vector<Weight>& weights, EqType rel, IntView* bound);

protected:
	virtual void setWeights(const std::vector<Weight>&);

private:
	virtual rClause notifypropagate();

	/**
	 * Similar to getMinAndMaxPossibleAggVals(), but without taking the excludedVar'th var into account.
	 * Hence returns a lower and upperbound of the aggregate with one variable excluded.
	 * If excludedVar is not in the range [0.._vars.size()[, returns a lower and upper bound for the entire aggregate
	 */
	std::pair<int, int> getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const;

	/**
	 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
	 * But excludes the excludedVar'th variable
	 */
	litlist varsContributingToMax(size_t excludedVar) const;
	litlist varsContributingToMin(size_t excludedVar) const;

	virtual AggType getType() const {
		return AggType::SUM;
	}

};

class FDProdConstraint: public FDAggConstraint {
private:
	Weight _weight;
	void initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel, IntView* bound);

public:

	// Product constraint: one weight for the whole expression, bound is an integer!
	FDProdConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel, const Weight& bound);
	// Product constraint: one weight for the whole expression, bound is a variable!
	FDProdConstraint(uint id, PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel, IntView* bound);

protected:
	virtual void setWeights(const std::vector<Weight>&);

private:
	/**
	 * Does propagation for products. The propagation is not complete, unless the product's value is known.
	 * If one of the variables can have negative values, propagation is done on the absolute values, otherwise, propagation on the real values is done.
	 */
	virtual rClause notifypropagate();

	/**
	 * Does complete propagation on products. Can only be called in case the value of the product is known!
	 * (i.e. iff getMinAndMaxPossibleAggVals() returns a pair with two times the same value)
	 * @param value
	 * The exact value of the aggregate (without incorporating the weight)
	 * @param boundvalue
	 * The exact value of the bound
	 */
	virtual rClause check(int value, int boundvalue);

	/**
	 * Propagation module for products where all variables are positive.
	 * @param min
	 * A lower bound on the value of the aggregate (without incorporating the weight)
	 * @param max
	 * An upper bound on the value of the aggregate (without incorporating the weight)
	 * @param minbound
	 * The minimum value for the bound
	 * @param maxbound
	 * The maximum value for the bound
	 */
	virtual rClause notifypropagateWithNeg(int min, int max, int minbound, int maxbound);

	/**
	 * Propagation for products where some variables can still take negative values.
	 * Propagation on the absolute values is implemented (incomplete)
	 * @param min
	 * A lower bound on the value of the aggregate (without incorporating the weight)
	 * @param max
	 * An upper bound on the value of the aggregate (without incorporating the weight)
	 * @param minbound
	 * The minimum value for the bound
	 * @param maxbound
	 * The maximum value for the bound
	 */
	virtual rClause notifypropagateWithoutNeg(int min, int max, int minbound, int maxbound);

	/**
	 * Similar to getMinAndMaxPossibleAggVals(), but without taking the excludedVar'th var into account.
	 * Hence returns a lower and upperbound of the aggregate with one variable excluded.
	 * If excludedVar is not in the range [0.._vars.size()[, returns a lower and upper bound for the entire aggregate
	 */
	std::pair<int, int> getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const;
	/**
	 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
	 * But excludes the excludedVar'th variable
	 */
	litlist varsContributingToMax(size_t excludedVar) const;
	litlist varsContributingToMin(size_t excludedVar) const;
	litlist varsContributingToAbsVal(size_t excludedVar) const;
	litlist varsContributingToAbsVal() const;

	litlist varsContributingToMax(size_t excludedVar, bool canBeNegative) const;
	litlist varsContributingToMin(size_t excludedVar, bool canBeNegative) const;

	/**
	 * Returns a vector of literals that represents that explains why this product cannot contain negatives
	 */
	litlist explainNotNegative();

	virtual AggType getType() const {
		return AggType::PROD;
	}
};
}
