/* * Copyright 2007-2011 Katholieke Universiteit Leuven * * Use of this software is governed by the GNU LGPLv3.0 license * * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium */
#ifndef DPLLTMODULE_HPP_
#define DPLLTMODULE_HPP_

#include "utils/Utils.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID {
enum State { PARSING, INITIALIZING, INITIALIZED };
class DPLLTmodule {
private:
	State init;

protected:
	PCSolver* pcsolver;

public:
	DPLLTmodule(PCSolver* s) :
		init(PARSING), pcsolver(s) {
	}
	virtual ~DPLLTmodule() {	}
	bool isParsing			() const { return init==PARSING; }	bool isInitializing 	() const { return init==INITIALIZING; }
	bool isInitialized		() const { return init==INITIALIZED; }	void notifyParsed		() { assert(isParsing()); init = INITIALIZING; }
	void notifyInitialized	() { assert(isInitializing()); init = INITIALIZED; }

	const PCSolver& getPCSolver() const { return *pcsolver; }
	PCSolver& getPCSolver() { return *pcsolver; }

	// DPLL-T methods

	virtual void notifyVarAdded(uint64_t nvars) = 0;
	virtual void finishParsing(bool& present, bool& unsat) = 0;
	virtual bool simplify() = 0; //False if problem unsat
	virtual rClause propagate(const Lit& l) = 0;
	virtual rClause propagateAtEndOfQueue() = 0;
	//virtual void 	backtrack				(const Lit& l) = 0;
	virtual void newDecisionLevel() = 0;
	virtual void backtrackDecisionLevels(int nblevels, int untillevel) = 0;

	/*
	 * Returns the explanation for the deduction of p from an aggregate expression.
	 * This method constructs, from the AggReason stored for it, a "reason clause" usable in clause learning.
	 * @post the first element in the reason clause will be the literal itself (invariant by minisat!)
	 * @post the clause is added to the sat solver
	 * @returns NON-OWNING pointer
	 */
	virtual rClause getExplanation(const Lit& l) = 0;

	virtual bool 	checkStatus() { return true; }

	virtual void printStatistics() const = 0;

	virtual const char* getName() const = 0;

	virtual void print() const = 0;

	// Convenience methods (based on getPCSolver)

	int 				verbosity() 			const { return getPCSolver().verbosity(); }
	const SolverOption& modes	() 				const { return getPCSolver().modes(); }

	bool 			isTrue		(const Lit& l) 	const { return value(l) == l_True; }
	bool 			isTrue		(Var v) 		const { return value(v) == l_True; }
	bool 			isFalse		(const Lit& l) 	const { return value(l) == l_False; }
	bool 			isFalse		(Var v) 		const {	return value(v) == l_False; }
	bool 			isUnknown	(const Lit& l) 	const { return value(l) == l_Undef; }
	bool 			isUnknown	(Var v) 		const { return value(v) == l_Undef; }
	lbool 			value		(Var x) 		const { return getPCSolver().value(x); }
	lbool 			value		(const Lit& p) 	const { return getPCSolver().value(p); }
	int 			nVars		() 				const {	return getPCSolver().nVars();	}
};

}

#endif /* DPLLTMODULE_HPP_ */
