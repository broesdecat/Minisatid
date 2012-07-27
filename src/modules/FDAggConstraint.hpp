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
	FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<Weight>& weights, EqType rel, const int& bound);
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
	std::pair<int,int> getMinAndMaxPossibleAggVals() const;
	std::pair<int,int> getMinAndMaxPossibleAggValsWithout(int varloc) const;

	bool containsNegatives() const;
	bool allDecided() const;
	virtual rClause notifypropagateSum();
	virtual rClause notifypropagateProd();
	virtual rClause checkProduct();
	virtual rClause notifypropagateProdWithNeg();
	virtual rClause notifypropagateProdWithoutNeg();

};

}

#endif //FD_AGG_CONSTRAINT_HPP
