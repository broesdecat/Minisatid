/*
 * LazyGrounder.hpp
 *
 *  Created on: May 30, 2011
 *      Author: broes
 */

#ifndef LAZYGROUNDER_HPP_
#define LAZYGROUNDER_HPP_

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

/*
 * How does it work:
 * have a vector with full clauses
 * have a vector with "grounded" clauses and an index of where we are in the full clause
 * make the grounded clauses 1-watched
 *
 * during propagate:
 * 		if a clause becomes fully false, extends its grounding until it can become true, set that as watch
 * 		if it cannot be made true any more, backtrack to the appropriate level and add the full clause to the solver
 */

namespace MinisatID{

class PCSolver;

class LazyGrounder: public Propagator{
private:
	InnerDisjunction clause;
	int indexinfullclause, indexinclausevector;
public:
	LazyGrounder(PCSolver* pcsolver);
	virtual ~LazyGrounder();

	bool	setClause(const InnerDisjunction& clause);

	// Propagator methods
	const char* getName			() const { return "lazy grounder"; }
	rClause getExplanation		(const Lit& l) { assert(false); return nullPtrClause; }
	rClause notifyFullAssignmentFound() { return nullPtrClause; }
	void 	finishParsing		(bool& present, bool& unsat) { return; }
	void 	notifyNewDecisionLevel	() { return; }
	void 	notifyBacktrack		(int untillevel, const Lit& decision) { return; }
	rClause	notifypropagate		();
	Var 	notifyBranchChoice	(const Var& var) const { return var; }
	void 	printStatistics		() const;
	void 	printState			() const {}
	int		getNbOfFormulas		() const { return 1; }
};
}

#endif /* LAZYGROUNDER_HPP_ */
