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

#include "solvers/utils/Utils.hpp"
#include "solvers/theorysolvers/LogicSolver.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

typedef std::vector<Lit> vlit;

namespace CP{
	class CPSolver;
}

using namespace CP;

class SolverOption;

class IDSolver;
class AggSolver;
class ModSolver;
class DPLLTmodule;

typedef Minisat::Solver* pSolver;
typedef IDSolver* pIDSolver;
typedef CPSolver* pCPSolver;
typedef AggSolver* pAggSolver;
typedef ModSolver* pModSolver;

enum Optim { MNMZ, SUBSETMNMZ, SUMMNMZ, NONE }; // Preference minimization, subset minimization, sum minimization

class DPLLTSolver{
private:
	DPLLTSolver(DPLLTSolver&){}
	DPLLTSolver& operator=(DPLLTSolver& m) { return m; }
public:
	DPLLTmodule* module;
	bool createdhere; //Indicates which solvers were constructed here and should be deleted later on by the pcsolver
	bool present; //Indicates whether the solver should be integrated into the search

	DPLLTSolver(DPLLTmodule* module, bool createdhere): module(module), createdhere(createdhere), present(true){}
	~DPLLTSolver();

	DPLLTmodule* get() const { return module; }
};

typedef std::vector<DPLLTSolver*> lsolvers;

class PCSolver: public MinisatID::LogicSolver{
private:
	//OWNING POINTER
	pSolver satsolver;

	// IMPORTANT: implicit invariant that IDsolver is always last in the list!
	lsolvers solvers;
	DPLLTSolver* idsolver;
	DPLLTSolver* aggsolver;
	DPLLTSolver* modsolver;

	IDSolver* getIDSolver() const;
	AggSolver* getAggSolver() const;
	ModSolver* getModSolver() const;

	int init;
	std::vector<Lit> initialprops;

	std::vector<DPLLTmodule*> propagations;

	///////
	// OPTIMIZATION INFORMATION
	///////
	Optim 		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	///////
	// FORCED CHOICES TO MAKE DURING SEARCH
	///////
	vec<Lit> forcedchoices;


	std::vector<int>	counts; //Number of occurences of each variable in the theory

	// Getters for solver pointers
	Minisat::Solver * 	getSolver	() const { return satsolver; }

public:
	PCSolver(SolverOption modes, MinisatID::WrappedLogicSolver* inter);
	virtual ~PCSolver();

	// Getters for constant solver pointers
	Minisat::Solver const *		getCSolver	() const { return satsolver; }
	lsolvers::const_iterator	getSolversBegin() const { return solvers.begin(); }
	lsolvers::const_iterator	getSolversEnd() const { return solvers.end(); }

	/*
	 * INITIALIZATION
	 */
	void 		setModSolver	(ModSolver* m);
	Var			newVar			();
	void		addVar			(Var v);
	bool 		addClause		(vec<Lit>& lits);
	bool 		addEquivalence	(const Lit& head, const vec<Lit>& rightlits, bool conj);
	bool 		addRule			(bool conj, Lit head, const vec<Lit>& lits);
	bool 		addSet			(int id, const vec<Lit>& lits);
	bool 		addSet			(int id, const vec<Lit>& lits, const std::vector<Weight>& w);
	bool 		addAggrExpr	(Lit head, int setid, const Weight& bound, AggSign boundsign, AggType type, AggSem defined);
	bool 		addIntVar		(int groundname, int min, int max);
	bool 		addCPBinaryRel	(Lit head, int groundname, EqType rel, int bound);
	bool 		addCPBinaryRelVar	(Lit head, int groundname, EqType rel, int groundname2);
	bool 		addCPSum		(Lit head, std::vector<int> termnames, EqType rel, int bound);
	bool 		addCPSum		(Lit head, std::vector<int> termnames, std::vector<int> mult, EqType rel, int bound);
	bool 		addCPSumVar		(Lit head, std::vector<int> termnames, EqType rel, int rhstermname);
	bool 		addCPSumVar		(Lit head, std::vector<int> termnames, std::vector<int> mult, EqType rel, int rhstermname);
	bool 		addCPCount		(std::vector<int> termnames, int value, EqType rel, int rhstermname);
	bool 		addCPAlldifferent(const std::vector<int>& termnames);

	void		addForcedChoices(const vec<Lit>& forcedchoices);

	void 		finishParsing	(bool& present, bool& unsat);

	///////
	// Solving support
	///////
	void 		newDecisionLevel();
	bool 		simplify();
	bool 		solve			(const vec<Lit>& assumptions, Solution* sol);
	lbool 		checkStatus		(lbool status) const; //if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status

	void		removeAggrHead	(Var x);
	void		notifyAggrHead	(Var head);

	bool 		assertedBefore	(const Var& l, const Var& p) const;
	rClause		getExplanation	(Lit l);	//NON-OWNING pointer

	int			getCount		(Var v)	const { return counts[v]; }

    ///////
	// Solver callbacks
	///////

	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	rClause 	createClause	(const vec<Lit>& lits, bool learned);
	//IMPORTANT: THE FIRST LITERAL IN THE CLAUSE HAS TO BE THE ONE WHICH CAN BE PROPAGATED FROM THE REST!!!!!!!
	void 		addLearnedClause(rClause c); //Propagate if clause is unit, return false if c is conflicting
	void    	backtrackTo		(int level);	// Backtrack until a certain level.
	void    	setTrue			(Lit p, DPLLTmodule* solver, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined
	rClause		makeClause		(vec<Lit>& lits, bool b);

	/**
	 * Allows to loop over all assignments made in the current decision level.
	 */
	const vec<Lit>& getTrail	() 		const;
	int 			getStartLastLevel() const;
	int 		getLevel		(int var) const; // Returns the decision level at which a variable was deduced.
	int			getNbDecisions	() 		const;
	uint64_t	getConflicts	() 		const;
	const vec<char>& getAssigns	()		const;

	int			getCurrentDecisionLevel	() const;
	std::vector<Lit>	getDecisions	() const;

	/*
	 * true if the current assignment is completely two-valued
	 * Cannot be const!
	 */
	bool 		totalModelFound	();

	void		varBumpActivity	(Var v);

	void 		backtrackRest	(Lit l);
	void 		backtrackDecisionLevel(int levels, int untillevel);
	rClause 	propagate		(Lit l);
	rClause 	propagateAtEndOfQueue();

	///////
	// OPTIMIZATION
	///////
    bool 	addMinimize		(const vec<Lit>& lits, bool subsetmnmz);
    bool 	addSumMinimize	(const Var head, const int setid);

	///////
	// DEBUG
	///////
	int		getModPrintID	() const;
	// SATsolver asks this to PC such that more info (modal e.g.) can be printed.
	void	printChoiceMade	(int level, Lit l) const;
	void 	printStatistics() const;

private:
	void addVar(Lit l) { addVar(var(l)); }
	void addVars(const vec<Lit>& a);
	void checkHead(Lit head);

	///////
	// SOLVING
	///////
	bool 		findNext		(const vec<Lit>& assumpts, vec<Lit>& model, bool& moremodels);
	bool    	invalidateModel	(vec<Lit>& invalidation);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(vec<Lit>& invalidation);
	bool 		findModel		(const vec<Lit>& assumps, vec<Lit>& m, bool& moremodels);

	///////
	// OPTIMIZATION
	///////
    bool 	invalidateValue	(vec<Lit>& invalidation);
	bool 	invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 	findOptimal		(const vec<Lit>& assumps, vec<Lit>& m);
};

}

#endif /* PCSOLVER_H_ */
