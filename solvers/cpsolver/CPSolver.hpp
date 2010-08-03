//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "solvers/pcsolver/ISolver.hpp"

namespace CP {

	class CPSolverData;

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
	class CPSolver: public ISolver {
	private:
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

	private:
		rClause propagateFinal();
	};

}

#endif /* CPSOLVER_HPP_ */
