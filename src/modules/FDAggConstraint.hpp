#pragma once

#include <vector>
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

struct Lit; // Note: To help eclipse indexer

// NOTE: always GEQ at the moment!
// 		_head <=> AGG >= _bound
class FDAggConstraint: public Propagator {
protected:
	Lit _head;
	std::vector<IntView*> _vars;
	IntView* _bound;
	std::vector<Lit> _conditions;

protected:
	FDAggConstraint(PCSolver* s, const std::string& name);
	virtual void setWeights(const std::vector<Weight>&) = 0;
	void sharedInitialization(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel, IntView* bound);
	void watchRelevantVars(); //sets all watches
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
	std::vector<Weight> _weights; // TODO weights can be dropped? TODO weights not infinite!
	void initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel, IntView* bound);

	// Sum only works on KNOWN bounds
	Weight getBound() const {
		return _bound->minValue();
	}

public:
	// Sum constraint: one weight for each var, where bound is an int.
	FDSumConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel, const Weight& bound);

private:
	friend class FDAggConstraint;
	friend class FDProdConstraint;
	// NOTE: bound has to have a KNOWN value!
	FDSumConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel, IntView* bound);

protected:
	virtual void setWeights(const std::vector<Weight>&);

private:
	virtual rClause notifypropagate();

	/**
	 * Similar to getMinAndMaxPossibleAggVals(), but without taking the excludedVar'th var into account.
	 * Hence returns a lower and upperbound of the aggregate with one variable excluded.
	 * If excludedVar is not in the range [0.._vars.size()[, returns a lower and upper bound for the entire aggregate
	 */
	inline std::pair<Weight, Weight> getMinAndMaxPossibleAggVals() const {
		return getMinAndMaxPossibleAggValsWithout(_vars.size());
	}
	std::pair<Weight, Weight> getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const;

	/**
	 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
	 * But excludes the excludedVar'th variable
	 */
	inline litlist varsContributingToMax(Weight bound) const {
		return varsContributingToMax(_vars.size(), bound);
	}
	inline litlist varsContributingToMin(Weight bound) const {
		return varsContributingToMin(_vars.size(), bound);
	}
	litlist varsContributingToMax(size_t excludedVar, Weight bound) const;
	litlist varsContributingToMin(size_t excludedVar, Weight bound) const;

	virtual AggType getType() const {
		return AggType::SUM;
	}

	enum class Contrib { MIN, MAX };
	rClause createClause(Contrib use, bool conflict, const std::vector<Lit>& extralits, Weight bound);
	rClause createClauseExcl(Contrib use, size_t varindex, bool conflict, const std::vector<Lit>& extralits, Weight bound);
};

class FDProdConstraint: public FDAggConstraint {
private:
	Weight _weight;
	Lit _definitelyPositive; //True if this agg is guaranteed to be positive

	void initialize(const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel, IntView* bound);

public:

	// Product constraint: one weight for the whole expression, bound is an integer!
	FDProdConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel, const Weight& bound);
	// Product constraint: one weight for the whole expression, bound is a variable!
	FDProdConstraint(PCSolver* engine, const Lit& head, const std::vector<Lit>& conditions, const std::vector<IntView*>& set, const Weight& weight, EqType rel, IntView* bound);

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
	virtual rClause check(Weight value, Weight boundvalue);

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
	virtual rClause notifypropagateWithNeg(Weight min, Weight max, Weight minbound, Weight maxbound);

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
	virtual rClause notifypropagateWithoutNeg(Weight min, Weight max, Weight minbound, Weight maxbound);

	/**
	 * Similar to getMinAndMaxPossibleAggVals(), but without taking the excludedVar'th var into account.
	 * Hence returns a lower and upperbound of the aggregate with one variable excluded.
	 * If excludedVar is not in the range [0.._vars.size()[, returns a lower and upper bound for the entire aggregate
	 */
	std::pair<Weight, Weight> getMinAndMaxPossibleAggVals() const {
		return getMinAndMaxPossibleAggValsWithout(_vars.size());
	}
	std::pair<Weight, Weight> getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const;
	/**
	 * Returns a list of all NEGATIONS OF variables contributing to the current maximum/minimum
	 * But excludes the excludedVar'th variable
	 */
	litlist varsContributingToMax(size_t excludedVar) const;
	litlist varsContributingToMin(size_t excludedVar) const;
	litlist varsContributingToAbsVal(size_t excludedVar) const;
	litlist varsContributingToAbsVal() const;

	litlist varsContributingToMax() const {
		return varsContributingToMax(_vars.size());
	}
	litlist varsContributingToMin() const {
		return varsContributingToMin(_vars.size());
	}

	litlist varsContributingToMax(size_t excludedVar, bool canBeNegative) const;
	litlist varsContributingToMin(size_t excludedVar, bool canBeNegative) const;

	/**
	 * This method returns true if and only if one of the variables can still take negative values
	 */
	bool canContainNegatives() const;

	virtual AggType getType() const {
		return AggType::PROD;
	}
};
}
