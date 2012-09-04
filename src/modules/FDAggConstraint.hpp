#ifndef FD_AGG_CONSTRAINT_HPP
#define FD_AGG_CONSTRAINT_HPP
#include <vector>
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

// NOTE: always GEQ at the moment!
// 		_head <=> AGG >= _bound
class FDAggConstraint: public Propagator {
private:
	Lit _head;
	std::vector<IntView*> _vars;
	std::vector<Weight> _weights; // If SUM: one for each var, if PROD: just one for the whole expression
	AggProp const * const _type;
	IntView* _bound;

	void sharedInitialization(AggType type, PCSolver* engine, const Lit& head, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
			IntView* bound);

	void initializeSum(PCSolver* engine, const Lit& head, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel, IntView* bound);
	void initializeProd(PCSolver* engine, const Lit& head, const std::vector<IntView*>& set, const Weight& weight, EqType rel, IntView* bound);

	// Sum constraint: one weight for each var, where bound is an intview.
	FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
			IntView* bound);
	// Product constraint: one weight for the whole expression, bound is an integer! TODO MOVE TO PUBLIC AGAIN OR DELETE
	FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const Weight& weight, EqType rel,
			const Weight& bound);

public:
	// Sum constraint: one weight for each var, where bound is an int.
	FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel,
			const int& bound);

	// Product constraint: one weight for the whole expression, bound is a variable!
	FDAggConstraint(uint id, PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const Weight& weight, EqType rel,
			IntView* bound);

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
	 * @param boundvalue
	 * The exact value of the bound
	 */
	virtual rClause checkProduct(int value, int boundvalue);

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
	virtual rClause notifypropagateProdWithNeg(int min, int max, int minbound, int maxbound);

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
	virtual rClause notifypropagateProdWithoutNeg(int min, int max, int minbound, int maxbound);

	/**
	 * Returns the unary negation of this bound (-bound)
	 */
	IntView* negation(IntView* bound);

	/**
	 * Creates an intview which can only take the value of bound.
	 */
	IntView* createBound(const Weight& min, const Weight& max);

	/**
	 * For every variable (different from the "excludedvar"),
	 * add lits that stand for Not the current absval situation.
	 * I.e. ,if in the current situation, a variable is in absolute value smaller than
	 * x, we add lits
	 * var < -x || var > x
	 *
	 * NOTE, excludedvarloc, can be a value that is bigger than (or equal to) the size of _vars,
	 * In that case, it means we don't want to exclude a variable
	 */
	void getLitsNotCurrentAbsValSituation(litlist& lits, uint excludedvarloc);

	/**
	 * Returns a vector of literals that represents
	 *   (v_1 \leq 0) \vee (v_2 \leq 0) \vee \cdots
	 * Where v_i are alle the vars in the aggregate
	 */
	litlist notAllVarsArePositive();
};

}

#endif //FD_AGG_CONSTRAINT_HPP
