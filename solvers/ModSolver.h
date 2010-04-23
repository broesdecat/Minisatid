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
#include "Solvers.h"
#include <stdio.h>

using namespace std;

class Solver;
class IDSolver;
class AggSolver;
class ModSolverData;

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

class ModSolver{
private:
	bool negated;
	int id, parentid;
	vector<AV> atoms; //atoms which are rigid within this solver
	vector<int> children;

	AV 		head;

	shared_ptr<Solver>		solver;
	shared_ptr<IDSolver>	idsolver;
	shared_ptr<AggSolver>	aggsolver;

	weak_ptr<ModSolverData> modhier;

public:
	ModSolver(bool neg, int id, Var head, const vector<Var>& a, shared_ptr<ModSolverData> mh);
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
	void	addVar			(int v);
	void 	addClause		(vec<Lit>& lits);
	void 	addRule			(bool conj, vec<Lit>& lits);
	void 	addSet			(int set_id, vec<Lit>& lits, vector<Weight>& w);
	void 	addAggrExpr		(int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined);
	//void 	finishDatastructures();

	//solver initialization
	//Solver*	initSolver		();
	//Solver*	initializeSolver(Theory& t);

	Var getHead()const {return head.atom;}
	int getId() const{return id;}
	int getParentId()const{return parentid;}
	//const Theory& getTheory()const{return theory;}
	const vector<AV>& getAtoms()const{return atoms;}
	const vector<int>& getChildren()const{return children;}
};

void printModSolver(const ModSolver* m);

#endif// MODSOLVER_H_
