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

	virtual void setNbModels	(int nb)	{ solver->nb_models=nb; }
	virtual void setRes			(FILE* f)	{ solver->res = f; }

	virtual bool simplify		()			{ return solver->simplify(); }
	virtual bool solve			()			{ return solver->solve(); }
	virtual void finishParsing(); //throws UNSAT

	void	addVar			(Var v);
	bool 	addClause		(vec<Lit>& lits);
	bool 	addRule			(bool conj, vec<Lit>& lits);
	bool 	addSet			(int set_id, vec<Lit>& lits, vector<Weight>& w);
	bool 	addAggrExpr		(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);

    void 	addMinimize(const vec<Lit>& lits, bool subsetmnmz);
    void 	addSumMinimize(const Var head, const int setid);
};

class ModSolverData: public Data, public enable_shared_from_this<ModSolverData>{
private:
	int nb_models;
	FILE* res;

	vector<pModSolver> solvers;

public:
	ModSolverData();
	~ModSolverData();

	virtual void setNbModels	(int nb)	{ nb_models=nb; }
	virtual void setRes			(FILE* f)	{ res = f; }

	virtual bool 	simplify		(){ return true;}
	virtual bool 	solve			();
	virtual void 	finishParsing	(){}
			void 	initialize		();

			void 	addVar			(Var v);
			bool 	addClause		(int modid, vec<Lit>& lits);
			bool 	addRule			(int modid, bool conj, vec<Lit>& lits);
			bool 	addSet			(int modid, int set_id, vec<Lit>& lits, vector<Weight>& w);
			bool 	addAggrExpr		(int modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);
			bool 	addChildren		(int modid, const vector<int>& children);
			bool 	addModSolver	(int modid, Var head, bool neg, const vector<Var>& atoms);

	pModSolver getModSolver(int modid){	return solvers[modid];	}

};

void initializeSolvers(pSolver& s, pIDSolver& is, pAggSolver& as);

#endif /* SOLVERS_H_ */
