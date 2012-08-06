#ifndef Solver_h
#define Solver_h

#include "MiniSat.h"
#include "Hardware.h"

namespace MiniSatPP {
//=================================================================================================

class Solver {
	MiniSat::Solver* minisat;

public:
	// Global clausification data:
	CMap<int> occ;
	CMap<Var> vmap;
	CMap<Lit,true> vmapp;

	Solver() : minisat(new MiniSat::Solver()), occ(0), vmap(var_Undef), vmapp(lit_Undef) {}
	~Solver(){
		delete(minisat);
	}
	bool& ok_ref () {return minisat->ok;}
	vec<int>& assigns_ref() {return minisat->assigns;}
	vec<Lit>& trail_ref () {return minisat->trail;}
	BasicSolverStats& stats_ref () {return (BasicSolverStats&)minisat->stats;}

	void setVerbosity(int level) {
		minisat->verbosity = level;}

	int numOfClouses () {return minisat->numOfClouses();}
	Var newVar (bool dvar = true) {return minisat->newVar(dvar);}
	bool addClause (const vec<Lit>& ps) {return minisat->addClause(ps);}
	bool addUnit (Lit p) {return minisat->addUnit(p);}
	void freeze (Var) {}
	void suggestPolarity(Var x, lbool value) {minisat->polarity_sug[x] = toInt(value);}
	bool solve (const vec<Lit>& assumps) {return minisat->solve(assumps);}
	bool solve () {vec<Lit> tmp; return solve(tmp);}
	vec<lbool>& model () {return minisat->model;}
	bool varElimed (Var) {return false;}
	bool okay () {return minisat->okay();}
	int nVars () {return minisat->nVars();}
	void exportCnf (cchar* filename) {
		minisat->simplifyDB();
		minisat->exportClauses(filename);
	}

	void toCNF(std::vector<std::vector<Lit> >& cnf) {
		minisat->simplifyDB();
		minisat->toCNF(cnf);

	}
};

//=================================================================================================
}
#endif
