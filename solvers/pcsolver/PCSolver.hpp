//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#ifndef PCSOLVER_H_
#define PCSOLVER_H_

#include "solvers/SolverI.hpp"
#include "solvers/utils/Utils.hpp"

using namespace std;

typedef vector<Lit> vlit;

//FIXME: the parser does -1, but +1 is always printed, also when NOT going through the parser

namespace CP{
	class CPSolver;
}

using namespace CP;

//TODO should create "ForWardDeclare SAT" file
#ifdef USEMINISAT
class Solver;
#endif
#ifdef USEMINISAT09Z
class Solver;
#endif
#ifdef USEMINISAT22
using namespace Minisat;
namespace Minisat{
	class Solver;
}
#endif

class IDSolver;
class AggSolver;
class ModSolver;

typedef Solver* pSolver;
typedef IDSolver* pIDSolver;
typedef CPSolver* pCPSolver;
typedef AggSolver* pAggSolver;
typedef ModSolver* pModSolver;


class PCSolver: public Data{
private:
	//OWNING POINTER
	pSolver solver;
	//OWNING POINTER
	pIDSolver idsolver;
	//OWNING POINTER
	pCPSolver cpsolver;
	//OWNING POINTER
	pAggSolver aggsolver;
	//NON-OWNING POINTER
	pModSolver modsolver;
	/*
	 * Indicates whether the solver was constructed
	 */
	bool aggcreated, idcreated, cpcreated;
	/*
	 * Indicates whether the solver should be integrated into the search
	 */
	bool aggsolverpresent, idsolverpresent, modsolverpresent, cpsolverpresent;

	int nb_models, modelsfound;

	int init;
	vector<Lit> initialprops;

	/*
	 * OPTIMIZATION INFORMATION
	 */
	MINIM		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	/*
	 * Getters for solver pointers
	 */
	Solver * 	getSolver		() const;
	IDSolver * 	getIDSolver		() const;
	CPSolver *	getCPSolver		() const;
	AggSolver *	getAggSolver	() const;
	ModSolver *	getModSolver	() const;

public:
	PCSolver(ECNF_mode modes);
	virtual ~PCSolver();

	/*
	 * Getters for constant solver pointers
	 */
	Solver	 const * getCSolver		() const;
	IDSolver const * getCIDSolver	() const;
	CPSolver const * getCCPSolver	() const;
	AggSolver const * getCAggSolver	() const;
	ModSolver const * getCModSolver	() const;

	/*
	 * INITIALIZATION
	 */
	void 		setModSolver	(pModSolver m);
	void 		setNbModels		(int nb);
	Var			newVar			();
	void		addVar			(Var v);
	bool 		addClause		(vec<Lit>& lits);
	bool 		addRule			(bool conj, Lit head, const vec<Lit>& lits);
	bool 		addSet			(int id, const vec<Lit>& lits);
	bool 		addSet			(int id, const vec<Lit>& lits, const vector<Weight>& w);
	bool 		addAggrExpr		(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined);
	bool 		addIntVar		(int groundname, int min, int max);
	bool 		addCPBinaryRel	(Lit head, int groundname, MINISAT::EqType rel, int bound);
	bool 		addCPBinaryRelVar	(Lit head, int groundname, MINISAT::EqType rel, int groundname2);
	bool 		addCPSum		(Lit head, vector<int> termnames, MINISAT::EqType rel, int bound);
	bool 		addCPSum		(Lit head, vector<int> termnames, vector<int> mult, MINISAT::EqType rel, int bound);
	bool 		addCPSumVar		(Lit head, vector<int> termnames, MINISAT::EqType rel, int rhstermname);
	bool 		addCPSumVar		(Lit head, vector<int> termnames, vector<int> mult, MINISAT::EqType rel, int rhstermname);
	bool 		addCPCount		(vector<int> termnames, int value, MINISAT::EqType rel, int rhstermname);
	bool 		addCPAlldifferent(const vector<int>& termnames);

	bool 		finishParsing	(); //throws UNSAT

	void 		newDecisionLevel();

	/*
	 * SOLVING
	 */
	bool 		simplify		();
	bool 		findNext		(const vec<Lit>& assumpts, vec<Lit>& model, bool& moremodels);
	bool    	invalidateModel	(vec<Lit>& invalidation);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(vec<Lit>& invalidation);
	bool 		solve			();
	bool 		solve			(vec<vec<Lit> >& models);
	bool		solve			(const vec<Lit>& assmpt);
	bool		solvenosearch	(const vec<Lit>& assmpt);
	bool 		solveAll		(vec<Lit>& assmpt);
	bool 		solveAll		(vec<Lit>& assmpt, vec<vec<Lit> >& models);

	void		removeAggrHead	(Var x);
	void		notifyAggrHead	(Var head);

	lbool 		checkStatus		(lbool status) const; //if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status
	rClause		getExplanation	(Lit l);	//NON-OWNING pointer

    /*
     * Solver callbacks
     */

	/*
	 * The definition is valid, so the idsolver can be removed from further propagations
	 * TODO what if the pcsolver is reset?
	 */
	void 		resetIDSolver	();

	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	//IMPORTANT: THE FIRST LITERAL IN THE CLAUSE HAS TO BE THE ONE WHICH CAN BE PROPAGATED FROM THE REST!!!!!!!
	rClause 	addLearnedClause(vec<Lit>& lits);	// don't check anything, just add it to the clauses and bump activity
	void    	backtrackTo		(int level);	// Backtrack until a certain level.
	void    	setTrue			(Lit p, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined
	rClause		makeClause		(vec<Lit>& lits, bool b);

	/**
	 * Allows to loop over all assignments made in the current decision level.
	 */
	vector<Lit> getRecentAssignments() const;
	/*
	 * Returns the decision level at which a variable was deduced. This allows to get the variable that was propagated earliest/latest
	 */
	int 		getLevel		(int var) const;
	int			getNbDecisions	() const;
	vector<Lit>	getDecisions	() const;
	uint64_t	getConflicts	() const;

	/*
	 * true if the current assignment is completely two-valued
	 * Cannot be const!
	 */
	bool 		totalModelFound	();

	void		varBumpActivity	(Var v);

	int decisionlevels;
	void 		backtrackRest	(Lit l);
	void 		backtrackDecisionLevel(int levels);
	rClause 	propagate		(Lit l);
	rClause 	propagateAtEndOfQueue();

	/*
	 * OPTIMIZATION
	 */
    bool 	addMinimize		(const vec<Lit>& lits, bool subsetmnmz);
    bool 	addSumMinimize	(const Var head, const int setid);
    bool 	invalidateValue	(vec<Lit>& invalidation);
	bool 	invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 	findOptimal		(vec<Lit>& assumps, vec<Lit>& m);

	/*
	 * DEBUG
	 */
	int		getModPrintID	() const;
	/*
	 * SATsolver asks this to PC such that more info (modal e.g.) can be printed.
	 */
	void	printChoiceMade	(int level, Lit l) const;

private:
	void addVar(Lit l) { addVar(var(l)); }
	void addVars(const vec<Lit>& a);
	void checkHead(Lit head);
};

tr1::shared_ptr<Data> unittest(ECNF_mode& modes);
tr1::shared_ptr<Data> unittest2(ECNF_mode& modes);

#endif /* PCSOLVER_H_ */
