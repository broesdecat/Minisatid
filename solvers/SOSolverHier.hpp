#ifndef SOSOLVER_H_
#define SOSOLVER_H_

#include "solvers/solverfwd.hpp"
#include "solvers/aggs/AggTypes.hpp"
#include "mtl/Vec.h"
#include "solvers/SolverI.hpp"
class Data;

/**
 * USEFUL EXTRA PROPAGATION RULES FROM PAPER An algorithm for QBF and experimental evaluation:
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

#include "solvers/ModSolver.hpp"
class ModSolver;
typedef ModSolver* pModSolver;

typedef vector<pModSolver> vmsolvers;
typedef vmsolvers::size_type modindex;

enum modhierstate {NEW, LOADINGHIER, LOADINGREST, ALLLOADED};

class ModSolverData: public Data, public enable_shared_from_this<ModSolverData>{
private:
	vmsolvers 	 solvers;
	modhierstate state;	//stores the current state of the parsing.

	/*PCSolver* propagationsolver;
	vector<Var> allAtoms;*/

public:
	ModSolverData				(ECNF_mode modes);
	virtual ~ModSolverData		();

	void	setNbModels			(int nb);
	void	setRes				(FILE* f);

	bool 	simplify			();
	bool 	solve				();

	bool 	finishParsing		();

	//Add information for hierarchy
	bool 	addChild			(modindex parent, modindex child, Lit head);
	void	addAtoms			(modindex modid, const vector<Var>& atoms);

	//Add information for PC-Solver
	void 	addVar				(modindex modid, Var v);
	bool 	addClause			(modindex modid, vec<Lit>& lits);
	bool 	addRule				(modindex modid, bool conj, vec<Lit>& lits);
	bool 	addSet				(modindex modid, int set_id, vec<Lit>& lits, vector<Weight>& w);
	bool 	addAggrExpr			(modindex modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);

	//Get information on hierarchy
	pModSolver getModSolver		(modindex modid) const { checkexistsModSolver(modid); return solvers[modid];}

private:
	void 	initialize			();
	void	verifyHierarchy		();
	void	checkexistsModSolver(modindex modid) const;
	bool	existsModSolver		(modindex modid) const { return modid<solvers.size() && solvers[modid]!=NULL; }
};

void print(const ModSolverData& d);

#endif /* SOSOLVER_H_ */
