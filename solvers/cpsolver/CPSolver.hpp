/*
 * CPSolver.hpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "solvers/pcsolver/PCSolver.hpp"

class PCSolver;

namespace CP {

	/**
	 * Class to interface with cp propagation (and who knows, search engines).
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
		bool 			init;
		PCSolver* 		pcsolver;
		CPSolverData* 	solverdata;

		vector<Lit> 	trail;

	public:
				CPSolver	(PCSolver * pcsolver);
		virtual ~CPSolver	();

		void 	addTerm		(int term, int min, int max);
		bool 	addAllDifferent(vector<int> term);
		void	addBinRel	(int groundname, MINISAT::EqType rel, int bound, int atom);
		void	addBinRelVar(int groundname, MINISAT::EqType rel, int groundname2, int atom);
		void 	addSum		(vector<int> term, MINISAT::EqType rel, int bound, int atom);
		void 	addSum		(vector<int> term, vector<int> mult, MINISAT::EqType rel, int bound, int atom);
		void 	addSumVar	(vector<int> term, MINISAT::EqType rel, int rhsterm, int atom);
		void 	addSumVar	(vector<int> term, vector<int>, MINISAT::EqType rel, int rhsterm, int atom);
		//void 	addCount	(vector<vector<string> > term, MINISAT::EqType rel, int value, int rhs);
		void 	addCount	(vector<int> terms, MINISAT::EqType rel, int value, int rhsterm);

		bool	finishParsing();

		rClause propagate	(Lit l);
		rClause propagateAtEndOfQueue();

		void 	backtrack	();
		void 	backtrack	(Lit l);

		PCSolver* getSolver() { return pcsolver; }

	private:
		rClause propagateFinal();
	};

}

#endif /* CPSOLVER_HPP_ */
