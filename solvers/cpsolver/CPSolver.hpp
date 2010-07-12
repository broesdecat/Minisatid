/*
 * CPSolver.hpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "solvers/PCSolver.hpp"

class PCSolver;

namespace CP {

/**
 * Class to interface with cp propagation (and who knows, search) engines.
 *
 * Interfacing with gecode:
 * 		include the correct hh files => http://www.gecode.org/doc-latest/reference/PageUsage.html
 *
 * 		gecode works as follows:
 * 			a "Space" obejct keeps the search space, domain, variables, ...
 * 			constraints, vars and domains can be added to the space
 * 			space has an operation "status" which propagates until fixpoint or failure
 */
class CPSolverData;

class CPSolver {
	bool init;
	PCSolver * pcsolver;
	CPSolverData* solverdata;
	//map<int, CPConstraint> mapatomtoexpr;
	//map<CPConstraint, int> mapexprtoatom;

public:
	CPSolver(PCSolver * pcsolver);
	virtual ~CPSolver();

	void addTerm(vector<string> term, int min, int max);
	void addAllDifferent(vector<vector<string> > term, int atom);
	void addSum(vector<vector<string> > term, MINISAT::EqType rel, int bound, int atom);

	Clause* propagate(Lit l);
	Clause* propagateAtEndOfQueue();

	void backtrack();

	bool finishParsing();

private:
	Clause* propagateFinal();
	/**
	 * Probably implement with a list of intvars, their original domains and a starting integer atom number
	 */
	//CPConstraint* findConstraint(Lit l);
	//Lit findAtom(CPConstraint* c);
};

}

#endif /* CPSOLVER_HPP_ */
