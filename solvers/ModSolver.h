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
class ModSolverHier;

class Data{
private:
	int nbmodels;
	FILE* res;
public:
	Data(){};
	virtual ~Data(){};

	virtual void setNbModels(int nb){ nbmodels = nb; }
	virtual void setRes(FILE* f){ res = f; }

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

	virtual void setRes(FILE* f){
		Data::setRes(f);
		m->res = f;
	}

	virtual bool simplify(){
		return m->simplify();
	}
	virtual bool solve(){
		return m->solve();
	}
	virtual void finishParsing(); //throws UNSAT
};

class ModSolverData: public Data{
private:
	shared_ptr<ModSolverHier> m;

public:
	ModSolverData(shared_ptr<ModSolverHier> m):Data(),m(m){};

	virtual bool simplify(){ return true;}
	virtual bool solve();
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

//FIXME: wel inductieve definities kunnen inlezen!

struct Theory{
	vector<A> aggrs;
	vector<C> clauses;
	vector<S> sets;
};

class ModSolver{
private:
	int id, parentid;
	vector<AV> atoms; //atoms which are rigid within this solver
	vector<int> children;

	AV 		head;
	Theory 	theory;

	weak_ptr<ModSolverHier> modhier;

public:
	ModSolver(int id, Var head, const vector<Var>& a, shared_ptr<ModSolverHier> mh):id(id),head(head), modhier(mh){
		for(int i=0; i<a.size(); i++){
			atoms.push_back(AV(a[i]));
		}
	}
	virtual ~ModSolver(){}

	void setChildren(const vector<Var>& a);
	void setParent(int id){
		parentid = id;
	}

	virtual bool solve();

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

	Var getHead()const {return head.atom;}
	int getId() const{return id;}
	int getParentId()const{return parentid;}
	const Theory& getTheory()const{return theory;}
	const vector<AV>& getAtoms()const{return atoms;}
	const vector<int>& getChildren()const{return children;}
};

class ExistentialModSolver: public ModSolver{
public:
	ExistentialModSolver(int id, Var head, const vector<Var>& a, shared_ptr<ModSolverHier> mh):ModSolver(id, head, a, mh){}
};

class UniversalModSolver: public ModSolver{
public:
	UniversalModSolver(int id, Var head, const vector<Var>& a, shared_ptr<ModSolverHier> mh):ModSolver(id, head, a, mh){}
};



class ModSolverHier: public enable_shared_from_this<ModSolverHier>{
private:
	vector<ModSolver* > solvers;

public:
	ModSolverHier();

	void initialize();

	void addModSolver(int modid, Var head, bool exist, const vector<Var>& atoms);

	ModSolver* getModSolver(int modid){
		return solvers[modid];
	}

	bool solve();
};

void printModSolver(const ModSolver* m);

#endif// MODSOLVER_H_
