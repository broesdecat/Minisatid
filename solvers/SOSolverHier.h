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
	//FIXME these are not yet used.
	int nb_models;
	FILE* res;

	vmsolvers solvers;

public:
	ModSolverData();	//HAVE to call initialize after constructor
	~ModSolverData();

	virtual void setNbModels	(int nb)	{ nb_models=nb; }
	virtual void setRes			(FILE* f)	{ res = f; }

	virtual bool 	simplify		();
	virtual bool 	solve			();
	virtual bool 	finishParsing	();
			void 	initialize		();

			void 	addVar			(Var v);
			bool 	addClause		(modindex modid, vec<Lit>& lits);
			bool 	addRule			(modindex modid, bool conj, vec<Lit>& lits);
			bool 	addSet			(modindex modid, int set_id, vec<Lit>& lits, vector<Weight>& w);
			bool 	addAggrExpr		(modindex modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);
			bool 	addChildren		(modindex modid, const vector<int>& children);
			bool 	addModSolver	(modindex modid, Lit head, const vector<Var>& atoms);

			bool	existsModSolver(modindex modid){ return modid<solvers.size() && solvers[modid]!=NULL; }
			pModSolver getModSolver(modindex modid){ assert(existsModSolver(modid));return solvers[modid];}

};

#endif /* SOSOLVER_H_ */
