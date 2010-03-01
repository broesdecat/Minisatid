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

class MODSolver;

struct Theory{
	vector<MODSolver*> children;
	vector<A> aggrs;
	vector<R> rules;
	vector<C> clauses;
	vector<S> sets;
};

class Solver;

class MODSolver {
private:
	int 	id;
	bool	forall;
	AV 		head;

	vector<AV> rigidatoms, modalatoms;
	Theory modaltheory, constrtheory;

	static MODSolver* root;
	static MODSolver* getModalOperator(int id, MODSolver& m);

public:
	static MODSolver* getModalOperator(int id);

	MODSolver(int id);
	virtual ~MODSolver();

	void setHead(int h){ head = h; }
	void setForall(bool f) { forall = f; }

	//Solve methods
	Clause* propagate(Lit l);
	bool 	canSearch();
	void 	backtrack(Lit l);
	Clause* getExplanation(Lit l);

	//modal initialization
	void 	addChild(MODSolver* m, bool constr);
	//void 	addRigidAtom	(Var a){ rigidatoms.push_back(AV(a)); }
	void 	addRigidAtoms	(vec<int>& atoms);
	void 	finishDatastructures();

	//data initialization
	void 	addRule			(bool constr, bool conj, vec<Lit>& lits);
	void 	addClause		(bool constr, vec<Lit>& lits);
	void 	addSet			(bool constr, int set_id, vec<Lit>& lits, vec<int>& w);
	void 	addAggrExpr		(bool constr, int defn, int set_id, int bound, bool lower, AggrType type, bool defined);

	vector<MODSolver*>::iterator beginModalChildren(){ return modaltheory.children.begin(); }
	vector<MODSolver*>::iterator endModalChildren(){ return modaltheory.children.end(); }
	vector<MODSolver*>::iterator beginConstrChildren(){ return constrtheory.children.begin(); }
	vector<MODSolver*>::iterator endConstrChildren(){ return constrtheory.children.end(); }
private:
	int 	getID			(){ return id; }

	void 	copyToVector	(vec<Lit>& lits, vector<Lit>& literals, bool constr);

	//solver initialization
	Solver*	initSolver		();
	Solver*	initializeExistsSolver();
	Solver*	initializeConstrSolver();
	Solver*	initializeModalSolver();
	Solver*	initializeSolver(Theory& t);
};

#endif /* MODSOLVER_H_ */
