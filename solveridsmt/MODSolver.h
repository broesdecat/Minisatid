/*
 * MODSolver.h
 *
 *  Created on: Feb 24, 2010
 *      Author: broes
 */

#ifndef MODSOLVER_H_
#define MODSOLVER_H_

#include <set>
#include <vector>
#include "Vec.h"
#include "SolverTypes.h"
#include "Solver.h"

struct AV{
	Var atom;
	lbool value;

	AV(Var a): atom(a), value(l_Undef){}

    bool operator == (AV p) const { return atom == p.atom; }
    bool operator != (AV p) const { return atom != p.atom; }
    bool operator <  (AV p) const { return atom < p.atom;  }
};

struct C{
	vector<Lit> lits;
};

struct R{
	bool conj;
	vector<Lit> lits;
};

struct S{
	int id;
	vector<Lit> lits;
	vector<int> weights;

};

struct A{
	bool lower, defined;
	int head, set, bound;
	AggrType type;
};

class Solver;

class MODSolver {
public:
	MODSolver();
	virtual ~MODSolver();

	Solver* constr, *mod;
	MODSolver* parent;
	vector<AV> rigidatoms, modalatoms;

	vector<A> constraggrs, modaggrs;
	vector<R> constrrules, modrules;
	vector<C> constrclauses, modclauses;
	vector<S> constrsets, modsets;

	bool forall;
	AV head;

	void addRigidAtom(Var a){
		rigidatoms.push_back(AV(a));
	}
	void addRule(bool constr, bool conj, vec<Lit>& lits);
	void addClause(bool constr, vec<Lit>& lits);
	void addSet(bool constr, int set_id, vec<Lit>& lits, vec<int>& w);
	void addAggrExpr(bool constr, int defn, int set_id, int bound, bool lower, AggrType type, bool defined);

	Clause* propagate(Lit l);
	bool canSearch();
	void backtrack(Lit l);
	Clause* getExplanation(Lit l);

	/*
	 * Initialization
	 */

	void subsetMinimize(vec<Lit>& lits);

	void finishDatastructures();

	void copyToVector(vec<Lit>& lits, vector<Lit> literals, bool constr);

	void solve();

	Solver* initSolver();
	Solver* initializeSolver(bool c);

};

#endif /* MODSOLVER_H_ */
