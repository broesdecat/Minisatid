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

#ifndef SOSOLVER_H_
#define SOSOLVER_H_

#include "solvers/utils/Utils.hpp"
#include "solvers/SolverI.hpp"

namespace MinisatID {

/**
 * USEFUL EXTRA PROPAGATION RULES FROM PAPER "An algorithm for QBF and experimental evaluation":
 *
 * forall reduction in qdimacs format: if a clause only contains universally quantified
 * literals, then it has to be a tautology or it is unsat (so anyway it can be dropped)
 * => need to store the quantifier of variables
 *
 * all clauses only containing existentially quantified vars have to be SAT or whole problem is UNSAT.
 * => SAT CALL
 * Initially, take all clauses only containing EQ vars.
 * Later, take all clauses containing EQ vars and decided UQ vars.
 * => Simulate by taking full theory, replace all literals = \lnot UQ var with a new var (#atoms+var), and make
 * 		all true that have not yet been decided.
 * Then incremental SAT solving with assumptions
 *
 * if the theory with all universally quantified vars dropped is SAT, then the whole theory is SAT
 * => SAT CALL
 * Initially, take all clauses with all UQ left out
 * Later, take all clauses containing EQ vars and decided UQ vars, leaving out the undecided ones.
 * => Simulate by taking full theory, replace all literals = \lnot AQ var with a new var (#atoms+var), and make
 * 		all false that have not yet been decided.
 * Then incremental SAT solving with assumptions
 *
 * monotone literals can be immediately assigned a value
 *
 * propagation if a clause only contains one existentially quantified literal and only later universally
 * quantified literals.
 *
 * something called pairwise falsity
 *
 */

class ModSolver;
typedef std::vector<ModSolver*> vmsolvers;

enum modhierstate {NEW, LOADINGHIER, LOADINGREST, ALLLOADED};

class ModSolverData: public MinisatID::Data{
private:
	vmsolvers 	 solvers;
	modhierstate state;	//stores the current state of the parsing.

public:
	ModSolverData				(ECNF_mode modes);
	virtual ~ModSolverData		();

	bool 	simplify			();

	void 	solve(InternSol* sol);

	bool 	finishParsing		();

	//Add information for hierarchy
	bool 	addChild			(vsize parent, vsize child, Lit head);
	bool	addAtoms			(vsize modid, const std::vector<Var>& atoms);

	//Add information for PC-Solver
	void 	addVar				(vsize modid, Var v);
	bool 	addClause			(vsize modid, vec<Lit>& lits);
	bool 	addRule				(vsize modid, bool conj, Lit head, vec<Lit>& lits);
	bool 	addSet				(vsize modid, int set_id, vec<Lit>& lits, std::vector<Weight>& w);
	bool 	addAggrExpr			(vsize modid, Lit head, int setid, Weight bound, AggSign boundsign, AggType type, AggSem defined);

	//Get information on hierarchy
	ModSolver* getModSolver		(vsize modid) const { checkexistsModSolver(modid); return solvers[modid];}

private:
	void	verifyHierarchy		();
	void	checkexistsModSolver(vsize modid) const;
	bool	existsModSolver		(vsize modid) const { return modid<solvers.size() && solvers[modid]!=NULL; }
};

}

#endif /* SOSOLVER_H_ */
