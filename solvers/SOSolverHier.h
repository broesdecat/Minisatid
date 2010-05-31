#ifndef SOSOLVER_H_
#define SOSOLVER_H_

#include "solverfwd.h"
#include "AggTypes.h"
#include "Vec.h"
#include "SolverI.h"
class Data;

#include "ModSolver.h"
class ModSolver;
typedef ModSolver* pModSolver;

typedef vector<pModSolver> vmsolvers;
typedef vmsolvers::size_type modindex;

class ModSolverData: public Data, public enable_shared_from_this<ModSolverData>{
private:
	vmsolvers solvers;

public:
	ModSolverData();	//HAVE to call initialize after constructor
	~ModSolverData();

	virtual void setNbModels	(int nb);
	virtual void setRes			(FILE* f);

	virtual bool 	simplify		();
	virtual bool 	solve			();
	virtual bool 	finishParsing	();
			void 	initialize		();

			void 	addVar			(modindex modid, Var v);
			bool 	addClause		(modindex modid, vec<Lit>& lits);
			bool 	addRule			(modindex modid, bool conj, vec<Lit>& lits);
			bool 	addSet			(modindex modid, int set_id, vec<Lit>& lits, vector<Weight>& w);
			bool 	addAggrExpr		(modindex modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);
			bool 	addChild		(modindex parent, modindex child, Lit head);
			void	addAtoms		(modindex modid, const vector<Var>& atoms);
			//bool 	addModSolver	(modindex modid, Lit head);

			bool	existsModSolver(modindex modid) const { return modid<solvers.size() && solvers[modid]!=NULL; }
			pModSolver getModSolver(modindex modid) const { assert(existsModSolver(modid));return solvers[modid];}
};

void print(const ModSolverData& d);

#endif /* SOSOLVER_H_ */
