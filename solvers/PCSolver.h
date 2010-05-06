#ifndef PCSOLVER_H_
#define PCSOLVER_H_

#include "SolverI.h"
#include "solverfwd.h"

#include <vector>

using namespace std;

typedef vector<Lit> vlit;


#include "Solver.h"
#include "IDSolver.h"
#include "AggSolver.h"
#include "ModSolver.h"

class Solver;
class IDSolver;
class AggSolver;
class ModSolver;

typedef Solver* pSolver;
typedef IDSolver* pIDSolver;
typedef AggSolver* pAggSolver;
typedef ModSolver* pModSolver;

class PCSolver: public Data{
private:
	pSolver solver;
	pIDSolver idsolver;
	pAggSolver aggsolver;
	pModSolver modsolver;
	bool aggsolverpresent, idsolverpresent, modsolverpresent;

	FILE* res;
	int nb_models, modelsfound;
	ECNF_mode modes;

	/****************************
	 * OPTIMIZATION INFORMATION *
	 ****************************/
	MINIM		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	const pSolver&		getSolver		() const;
	const pIDSolver& 	getIDSolver		() const;
	const pAggSolver& 	getAggSolver	() const;
	const pModSolver& 	getModSolver	() const;

public:
	PCSolver(ECNF_mode modes);
	~PCSolver();

	void 	setModSolver(pModSolver m);

	void 	setNbModels		(int nb);
	void 	setRes			(FILE* f);

	Var		newVar			();
	void	addVar			(Var v);
	void 	addVars			(vec<Lit>& a);
	bool 	addClause		(vec<Lit>& lits);
	bool 	addRule			(bool conj, vec<Lit>& lits);
	bool 	addSet			(int set_id, vec<Lit>& lits, vector<Weight>& w);
	bool 	addAggrExpr		(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);
	bool 	finishParsing	(); //throws UNSAT

	bool 	simplify		();
	bool 	simplifyRest		();
	bool 	findNext		(const vec<Lit>& assumpts, vec<Lit>& model);
	bool    invalidateModel	(vec<Lit>& invalidation);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 	invalidate		(vec<Lit>& invalidation);
	bool 	solve			();
	bool	solve(const vec<Lit>& assmpt);
	void 	printModel		() const;

	void	removeAggrHead	(Var x);
	void	notifyAggrHead	(Var head);

	lbool 	checkStatus		(lbool status) const; //if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status
	Clause* getExplanation	(Lit l);

    /**************************
     * NECESSARY FOR IDSOLVER *
     **************************/

	void 	resetIDSolver	();

	lbool   value			(Var x) const;		// The current value of a variable.
	lbool   value			(Lit p) const;		// The current value of a literal.
	int     nVars			()      const;		// The current number of variables.

	//IMPORTANT: THE FIRST LITERAL IN THE CLAUSE HAS TO BE THE ONE WHICH CAN BE PROPAGATED FROM THE REST!!!!!!!
	void 	addLearnedClause(Clause* c);	// don't check anything, just add it to the clauses and bump activity
	void    backtrackTo		(int level);	// Backtrack until a certain level.
	void    setTrue			(Lit p, Clause* c = NULL);		// Enqueue a literal. Assumes value of literal is undefined

	/*
	 * Returns the decision level at which a variable was deduced. This allows to get the variable that was propagated earliest/latest
	 */
	int 	getLevel		(int var) const;

	/**
	 * Allows to loop over all assignments made in the current decision level.
	 */
	vector<Lit> 	getRecentAssignments() const;

	bool 	totalModelFound();				//true if the current assignment is completely two-valued

	int		getConflicts	();

	void     printClause	(const Clause& c);

	/***************************
	 * NECESSARY FOR AGGSOLVER *
	 ***************************/

	void 	resetAggSolver	();
	void	varBumpActivity	(Var v);		// Increase a variable with the current 'bump' value.

	/************************
	 * NECESSARY FOR SOLVER *
	 ************************/

	void 	backtrackRest	(Lit l);
	Clause* propagate		(Lit l);
	Clause* propagateDefinitions();

	/****************
	 * OPTIMIZATION *
	 ****************/

    bool 	addMinimize		(const vec<Lit>& lits, bool subsetmnmz);
    bool 	addSumMinimize	(const Var head, const int setid);
    bool 	invalidateValue	(vec<Lit>& invalidation);
	bool 	invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 	findOptimal		(vec<Lit>& assumps, vec<Lit>& m);
};

#endif /* PCSOLVER_H_ */
