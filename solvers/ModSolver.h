#ifndef MODSOLVER_H_
#define MODSOLVER_H_

#include <set>
#include <vector>
#include <tr1/memory>
#include "Vec.h"
#include "SolverTypes.h"
#include "Solver.h"
#include "IDSolver.h"
#include "AggSolver.h"
#include <stdio.h>

using namespace std;
using namespace tr1;

class ModSolver;
class Solver;
class IDSolver;
class AggSolver;

class Data{
private:
	int nbmodels;
	FILE* res;
public:
	Data(){};
	virtual ~Data(){};

	virtual void setNbModels(int nb){ nbmodels = nb; }
	void setRes(FILE* f){ res = f; }

	virtual bool simplify() = 0;
	virtual bool solve() = 0;
	virtual void finishParsing() = 0;
};

class SolverData: public Data{
private:
	shared_ptr<Solver> m;
	shared_ptr<IDSolver> md;
	shared_ptr<AggSolver> ma;

public:
	SolverData(shared_ptr<Solver> m, shared_ptr<IDSolver> md, shared_ptr<AggSolver> ma):Data(),m(m), md(md), ma(ma){};

	virtual void setNbModels(int nb){
		Data::setNbModels(nb);
		m->nb_models=nb;
	}

	virtual bool simplify(){
		return m->simplify();
	}
	virtual bool solve(){
		return m->solve();
	}
	virtual void finishParsing();
};

class ModSolverData: public Data{
private:
	shared_ptr<ModSolver> m;

public:
	ModSolverData(shared_ptr<ModSolver> m):Data(),m(m){};

	virtual bool simplify(){ return false;}
	virtual bool solve(){ return false; }
	virtual void finishParsing(){}
};

/**
 * Each modsolver has an id, a parent and a number of children
 * The topmost solver has no parent and id 0 and is created the moment the header is parsed
 *
 * The ids are substracted by one to get their position in the vector
 *
 * parsing process:
 * read statements of the form
 * A ID1 ID2 ATOM* 0 or E ID1 ID2 ATOM* 0
 * indicating a forall (A) or existantial (E) quantification of the atoms in ATOM* for a modal solver ID1 with parent ID2
 */

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

struct S{
	int id;
	vector<Lit> lits;
	vector<Weight> weights;

};

struct A{
	bool lower, defined;
	int head, set;
	Weight bound;
	AggrType type;
};

struct Theory{
	vector<A> aggrs;
	vector<C> clauses;
	vector<S> sets;
};

class ModSolver{
private:
	int id;
	vector<AV> atoms; //atoms which are rigid within this solver

	AV 		head;
	Theory 	theory;

public:
	ModSolver(int id, Var head, const vec<Lit>& a):id(id),head(head){
		for(int i=0; i<a.size(); i++){
			atoms.push_back(AV(var(a[i])));
		}
	}
	virtual ~ModSolver(){}

	/*//Solve methods
	Clause* propagate(Lit l);
	bool 	canSearch();
	void 	backtrack(Lit l);
	Clause* getExplanation(Lit l);*/

	//data initialization
	void 	addClause		(const vec<Lit>& lits);
	void 	addSet			(int set_id, const vec<Lit>& lits, const vector<Weight>& w);
	void 	addAggrExpr		(int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined);
	//void 	finishDatastructures();

	//solver initialization
	//Solver*	initSolver		();
	//Solver*	initializeSolver(Theory& t);
};

class ExistentialModSolver: public ModSolver{
public:
	ExistentialModSolver(int id, Var head, const vec<Lit>& a):ModSolver(id, head, a){}
};

class UniversalModSolver: public ModSolver{
public:
	UniversalModSolver(int id, Var head, const vec<Lit>& a):ModSolver(id, head, a){}
};



class ModSolverHier{
private:
	vector<shared_ptr<ModSolver> > solvers;

public:
	ModSolverHier();

	void addModSolver(int modid, Var head, bool exist, const vec<Lit>& atoms);

	shared_ptr<ModSolver> getModSolver(int modid){return solvers[modid];}
};

#endif MODSOLVER_H_

//class MODSolver {
//private:
//	int 	id;
//	bool	forall;
//	AV 		head;
//
//	vector<AV> rigidatoms, modalatoms;
//	Theory modaltheory, constrtheory;
//
//	static MODSolver* root;
//	static MODSolver* getModalOperator(int id, MODSolver& m);
//
//public:
//	static MODSolver* getModalOperator(int id);
//
//	MODSolver(int id);
//	virtual ~MODSolver();
//
//	void setHead(int h){ head = h; }
//	void setForall(bool f) { forall = f; }
//
//	//Solve methods
//	Clause* propagate(Lit l);
//	bool 	canSearch();
//	void 	backtrack(Lit l);
//	Clause* getExplanation(Lit l);
//
//	//modal initialization
//	void 	addChild(MODSolver* m, bool constr);
//	//void 	addRigidAtom	(Var a){ rigidatoms.push_back(AV(a)); }
//	void 	addRigidAtoms	(vec<int>& atoms);
//	void 	finishDatastructures();
//
//	//data initialization
//	void 	addRule			(bool constr, bool conj, vec<Lit>& lits);
//	void 	addClause		(bool constr, vec<Lit>& lits);
//	void 	addSet			(bool constr, int set_id, vec<Lit>& lits, vec<Weight>& w);
//	void 	addAggrExpr		(bool constr, int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined);
//
//	vector<MODSolver*>::iterator beginModalChildren(){ return modaltheory.children.begin(); }
//	vector<MODSolver*>::iterator endModalChildren(){ return modaltheory.children.end(); }
//	vector<MODSolver*>::iterator beginConstrChildren(){ return constrtheory.children.begin(); }
//	vector<MODSolver*>::iterator endConstrChildren(){ return constrtheory.children.end(); }
//private:
//	int 	getID			(){ return id; }
//
//	void 	copyToVector	(vec<Lit>& lits, vector<Lit>& literals, bool constr);
//
//	//solver initialization
//	Solver*	initSolver		();
//	Solver*	initializeExistsSolver();
//	Solver*	initializeConstrSolver();
//	Solver*	initializeModalSolver();
//	Solver*	initializeSolver(Theory& t);
//};
//
