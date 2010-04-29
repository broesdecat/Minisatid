#ifndef SOLVERS_H_
#define SOLVERS_H_

#include <tr1/memory>

#include <vector>
#include "Vec.h"

#include "SolverTypes.h"
#include "Solver.h"
#include "IDSolver.h"
#include "AggSolver.h"
#include "ModSolver.h"

class Solver;
class IDSolver;
class AggSolver;
class ModSolver;

typedef shared_ptr<Solver> pSolver;
typedef shared_ptr<IDSolver> pIDSolver;
typedef shared_ptr<AggSolver> pAggSolver;
typedef ModSolver* pModSolver;

class Data{
public:
	Data(){};
	virtual ~Data(){};

	virtual void setNbModels(int nb) = 0;
	virtual void setRes(FILE* f) = 0;

	virtual bool 	simplify() = 0;
	virtual bool 	solve() = 0;
	virtual void 	finishParsing() = 0;
};

class SolverData: public Data{
private:
	pSolver solver;
	pIDSolver idsolver;
	pAggSolver aggsolver;

public:
	SolverData();

	virtual void setNbModels	(int nb);
	virtual void setRes			(FILE* f);

	virtual bool simplify		();
	virtual bool solve			();
	virtual void finishParsing(); //throws UNSAT

	void	addVar			(Var v);
	bool 	addClause		(vec<Lit>& lits);
	bool 	addRule			(bool conj, vec<Lit>& lits);
	bool 	addSet			(int set_id, vec<Lit>& lits, vector<Weight>& w);
	bool 	addAggrExpr		(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);

    bool 	addMinimize(const vec<Lit>& lits, bool subsetmnmz);
    bool 	addSumMinimize(const Var head, const int setid);
};

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
	virtual void 	finishParsing	();
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

void initializeSolvers(pSolver& s, pIDSolver& is, pAggSolver& as);

#endif /* SOLVERS_H_ */
