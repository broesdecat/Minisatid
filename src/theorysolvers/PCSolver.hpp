/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PCSOLVER_H_
#define PCSOLVER_H_

#include "utils/Utils.hpp"
#include "theorysolvers/LogicSolver.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class SolverOption;

class IDSolver;
class AggSolver;
class ModSolver;
class DPLLTmodule;

typedef Minisat::Solver* pSolver;
typedef IDSolver* pIDSolver;
typedef AggSolver* pAggSolver;
typedef ModSolver* pModSolver;

enum Optim { MNMZ, SUBSETMNMZ, AGGMNMZ, NONE }; // Preference minimization, subset minimization, sum minimization

class PCLogger{
private:
	std::vector<int> occurrences;
	int propagations;

public:
	PCLogger();

	void addPropagation() { propagations++; }
	int getNbPropagations() const { return propagations; }
	void addCount(Var v);
	int getCount(Var v) const;

};

class PCSolver;

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

typedef std::vector<DPLLTSolver*> solverlist;

class PCSolver: public MinisatID::LogicSolver{
private:
	//OWNING POINTER
	pSolver satsolver;

	// IMPORTANT: implicit invariant that IDsolver is always last in the list!
	solverlist solvers;
	DPLLTSolver* idsolver;
	DPLLTSolver* aggsolver;
	DPLLTSolver* modsolver;

	IDSolver* getIDSolver() const;
	ModSolver* getModSolver() const;

	bool initialized;
	std::vector<Lit>		initialprops;

	std::vector<DPLLTmodule*> propagations;

	// OPTIMIZATION INFORMATION
	Optim 		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	// FORCED CHOICES TO MAKE DURING SEARCH
	vec<Lit> forcedchoices;

	//Logging
	PCLogger* logger;

	Minisat::Solver * 	getSolver	() const { return satsolver; }

public:
	PCSolver(SolverOption modes, MinisatID::WLSImpl& inter);
	virtual ~PCSolver();

	solverlist::const_iterator	getSolversBegin() const { return solvers.begin(); }
	solverlist::const_iterator	getSolversEnd() const { return solvers.end(); }

	AggSolver* getAggSolver() const;

	// INIT
	void 		setModSolver	(ModSolver* m);

	Var			newVar			();
	void		addVar			(Var v);
	bool 		addClause		(vec<Lit>& lits);
	bool 		addEquivalence	(const Lit& head, const vec<Lit>& rightlits, bool conj);
	bool 		addRule			(bool conj, Lit head, const vec<Lit>& lits);
	bool 		addRuleToID		(int defid, bool conj, Lit head, const vec<Lit>& lits);
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

    bool 		addMinimize		(const vec<Lit>& lits, bool subsetmnmz);
    bool 		addMinimize		(const Var head, const int setid, AggType agg);

	// Solving support
	void 		newDecisionLevel();
	void 		finishParsing	(bool& present, bool& unsat);
	bool 		simplify();
	bool 		solve			(const vec<Lit>& assumptions, const ModelExpandOptions& options);
	lbool 		checkStatus		(lbool status) const; //if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status

	void		removeAggrHead	(Var x);
	void		notifyAggrHead	(Var head);

	bool 		assertedBefore	(const Var& l, const Var& p) const;
	rClause		getExplanation	(Lit l);	//NON-OWNING pointer


    // Solver callbacks
	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	rClause 	createClause	(const vec<Lit>& lits, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void 		addLearnedClause(rClause c); //Propagate if clause is unit, return false if c is conflicting
	void    	backtrackTo		(int level);	// Backtrack until a certain level.
	void    	setTrue			(Lit p, DPLLTmodule* solver, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined

	const vec<Lit>& getTrail	() 		const;
	int 		getStartLastLevel() 	const;
	int 		getLevel		(int var) const; // Returns the decision level at which a variable was deduced.
	int			getNbDecisions	() 		const;

	int			getCurrentDecisionLevel	() const;
	std::vector<Lit>	getDecisions() 	const;

	bool 		totalModelFound	(); //cannot be const!

	void		varBumpActivity	(Var v);

	void 		backtrackRest	(Lit l);
	void 		backtrackDecisionLevel(int levels, int untillevel);
	rClause 	propagate		(Lit l);
	rClause 	propagateAtEndOfQueue();

	void 	printCurrentOptimum(const Weight& value) const;

	// DEBUG
	void	printModID() const; // SATsolver asks this to PC such that more info (modal e.g.) can be printed.
	void 	printEnqueued(const Lit& p) const;
	void	printChoiceMade	(int level, Lit l) const;
	void 	printStatistics() const;
	void	print() const;
	void	print(rClause clause) const;

	const PCLogger& getLogger() const { return *logger; }

private:
	void addVar(Lit l) { addVar(var(l)); }
	void addVars(const vec<Lit>& a);
	void checkHead(Lit head);

	// SOLVING
	bool 		findNext		(const vec<Lit>& assumpts, vec<Lit>& model, bool& moremodels);
	bool    	invalidateModel	(vec<Lit>& invalidation);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(vec<Lit>& invalidation);
	bool 		findModel		(const vec<Lit>& assumps, vec<Lit>& m, bool& moremodels);

	// OPTIMIZATION
    bool 	invalidateValue	(vec<Lit>& invalidation);
	bool 	invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 	findOptimal		(const vec<Lit>& assumps, vec<Lit>& m);
};

}

#endif /* PCSOLVER_H_ */
