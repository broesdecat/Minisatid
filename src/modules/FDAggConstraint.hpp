#ifndef FD_AGG_CONSTRAINT_HPP
#define FD_AGG_CONSTRAINT_HPP
#include <vector>
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

// NOTE: always GEQ at the moment!
// Always: AGG >= BOUND
class FDAggConstraint: public Propagator {
private:
	Lit _head;
	std::vector<IntView*> _vars;
	std::vector<Weight> _weights; // If SUM: one for each var, if PROD: just one for the whole expression
	AggProp const * const _type;
	Weight _bound;

	void sharedInitialization(AggType type, PCSolver* engine, const Lit& head, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
			const Weight& bound);
public:
	// Sum constraint: one weight for each var
	FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
			const int& bound);
	// Product constraint: one weight for the whole expression
	FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const Weight& weight, EqType rel, const int& bound);

	// Propagator methods
	virtual int getNbOfFormulas() const {
		return 1;
	}

	virtual rClause notifypropagate();
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
private:
	virtual rClause notifypropagateSum();

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
	std::pair<int, int> getMinAndMaxPossibleAggValsWithout(size_t excludedVar) const;

	/**
	 * This method returns true if and only if one of the variables can still take negative values
	 */
	bool canContainNegatives() const;

	/**
	 * Does propagation for products. The propagation is not complete, unless the product's value is known.
	 * If one of the variables can have negative values, propagation is done on the absolute values, otherwise, propagation on the real values is done.
	 */
	virtual rClause notifypropagateProd();

	/**
	 * Does complete propagation on products. Can only be called in case the value of the product is known!
	 * (i.e. iff getMinAndMaxPossibleAggVals() returns a pair with two times the same value)
	 * @param value
	 * The exact value of the aggregate (without incorporating the weight)
	 */
	virtual rClause checkProduct(int value);

	/**
	 * Propagation module for products where all variables are positive.
	 * @param min
	 * A lower bound on the value of the aggregate (without incorporating the weight)
	 * @param max
	 * An upper bound on the value of the aggregate (without incorporating the weight)
	 */
	virtual rClause notifypropagateProdWithNeg(int min, int max);

	/**
	 * Propagation for products where some variables can still take negative values.
	 * Propagation on the absolute values is implemented (incomplete)
	 * @param min
	 * A lower bound on the value of the aggregate (without incorporating the weight)
	 * @param max
	 * An upper bound on the value of the aggregate (without incorporating the weight)
	 */
	virtual rClause notifypropagateProdWithoutNeg(int min, int max);

};

}

#endif //FD_AGG_CONSTRAINT_HPP
