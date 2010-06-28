#ifndef MODSOLVER_H_
#define MODSOLVER_H_

#include <set>
#include <vector>
#include <tr1/memory>
#include "Vec.h"
#include "SolverTypes.hpp"
#include "solvers/PCSolver.hpp"
#include "solvers/SOSolverHier.hpp"
#include <stdio.h>

using namespace std;

class PCSolver;
typedef PCSolver* pPCSolver;

class ModSolverData;

class ModSolver;
typedef ModSolver* pModSolver;

typedef vector<pModSolver> vmsolvers;
typedef vmsolvers::size_type modindex;
typedef vector<modindex> vmodindex;

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

/*    bool operator == (AV p) const { return atom == p.atom; }
    bool operator != (AV p) const { return atom != p.atom; }
    bool operator <  (AV p) const { return atom < p.atom;  }*/
};

class ModSolver{
private:
	bool hasparent, searching, init; //, startedsearch;

	AV			head;
	vector<Var>	atoms; //atoms which are rigid within this solver

	modindex 	id, parentid;
	pPCSolver	solver;
	vmodindex 	children;
	weak_ptr<ModSolverData> modhier;

	vec<Lit> 	assumptions;
	//int			startindex;
	vector<bool> propfromabove; //Indicates whether this literal was propagated by the parent

public:
	ModSolver(modindex child, Var head, shared_ptr<ModSolverData> mh);
	virtual ~ModSolver();

	void 	addAtoms		(const vector<Var>& atoms);
	void 	addChild		(modindex child);
	void	setParent		(modindex id);

	void 	setNbModels		(int nb);
	void 	setRes			(FILE* f);

	/*//Solve methods
	Clause* propagate(Lit l);
	bool 	canSearch();
	void 	backtrack(Lit l);
	Clause* getExplanation(Lit l);*/

	//data initialization
	void				addVar			(Var v);
	bool 				addClause		(vec<Lit>& lits);
	bool 				addRule			(bool conj, vec<Lit>& lits);
	bool 				addSet			(int setid, vec<Lit>& lits, vector<Weight>& w);
	bool 				addAggrExpr		(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);
	bool 				finishParsing();

	//solver initialization
	//Solver*	initSolver		();
	//Solver*	initializeSolver(Theory& t);

	/**
	 * Workflow: parents propagates some literal down
	 * if not all rigid atoms or head known:
	 * 		do unit propagation in sat solver
	 * 		after unit propagation: any new rigid atom/head propagations are propagated UP
	 *
	 * if all rigid atoms and head are known
	 * 		search in sat solver
	 * 		this can only results in conflicts, not in new propagations
	 *
	 * propagate by sat solver -> propagate in this mod solver by propagating it to all modal solvers.
	 *
	 * SAT-solver should contains all atoms occurring in its theory, all heads of the children and all
	 * rigid atoms of the children. It should also decide them all.
	 *
	 * The model of a theory is the interpretation of all atoms decided by the root SAT solver.
	 */
	void 				printModel();

	/**
	 * Propagation coming from the parent solver: propagate it through the tree, until a conflict is found.
	 * SHOULD also return unit propagated implied rigid atoms.
	 */
	Clause* 			propagateDown(Lit l);
	Clause* 			propagateDownAtEndOfQueue();
	/**
	 * Propagation coming from the sat-solver: should propagate it through all modal solvers.
	 *
	 * Should NOT be called from other sources than the SAT-solver.
	 */
	Clause* 			propagate(Lit l);
	Clause* 			propagateAtEndOfQueue();
	/**
	 * Same as enqueue or notifyofpropagation: add it to the sat-solver queue, but remember why it was
	 * propagated. Id indicates from which modal solver the propagation came.
	 * to ask an explanation later on.
	 */
	void 				propagateUp(Lit l, modindex id);

	bool 				simplify();

	void 				backtrackFromAbove(Lit l);
	void 				backtrackFromSameLevel(Lit l);

	/**
	 * This will be difficult to implement?
	 */
	Clause* 			getExplanation(Lit l);

	bool				hasParent	()	const 	{ return hasparent; }
	Var 				getHead		()	const 	{ assert(hasparent); return head.atom; }
	lbool 				getHeadValue()	const	{ assert(hasparent); return head.value; }
	modindex 			getId		()	const	{ return id; }
	int		 			getPrintId	()	const	{ return id+1; }
	modindex			getParentId	()	const	{ return parentid; }
	int					getParentPrintId	()	const	{ return parentid+1; }
	const vector<Var>& 	getAtoms	()	const	{ return atoms; }
	const vmodindex& 	getChildren	()	const	{ return children; }

	const ModSolverData& getModSolverData() const	{ return *modhier.lock().get(); }
	PCSolver const * const getCPCSolver	()	const	{ return solver; }

	bool 				solve();

private:
	pPCSolver 			getSolver	()	const	{ return solver; }

	void 				addVars		(vec<Lit>& a);

	void				adaptValuesOnPropagation(Lit l);
	void 				doUnitPropagation	(const vec<Lit>&);
	bool 				search				(const vec<Lit>&, bool search = true);
	Clause* 			analyzeResult		(bool result, bool allknown);
};

#endif// MODSOLVER_H_
