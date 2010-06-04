#ifndef SOSOLVER_H_
#define SOSOLVER_H_

#include "solverfwd.hpp"
#include "AggTypes.hpp"
#include "Vec.h"
#include "SolverI.hpp"
class Data;

#include "ModSolver.hpp"
class ModSolver;
typedef ModSolver* pModSolver;

typedef vector<pModSolver> vmsolvers;
typedef vmsolvers::size_type modindex;

enum modhierstate {NEW, LOADINGHIER, LOADINGREST, ALLLOADED};

class ModSolverData: public Data, public enable_shared_from_this<ModSolverData>{
private:
	vmsolvers 	 solvers;
	modhierstate state;	//stores the current state of the parsing.

public:
	ModSolverData				();
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
