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

#include "theorysolvers/PropagatorFactory.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class CPSolver;
class ModSolver;
class SolverOption;
class Propagator;
class PropagatorFactory;
class EventQueue;
class SearchMonitor;
class IntVar;
typedef Minisat::Solver SearchEngine;

enum Optim { MNMZ, SUBSETMNMZ, NONE }; // Preference minimization, subset minimization, sum minimization

enum TheoryState {THEORY_PARSING, THEORY_INITIALIZED, THEORY_INITIALIZING};


class PCSolver: public MinisatID::LogicSolver{
private:
	int	ID;
	int getID() const { return ID+1; }

	//Search algorithms //TODO refactor into an interface "searchalgorithm" with subclasses satsolver and cpsolver?
	SearchEngine* searchengine;
	SearchEngine& getSolver() { return *searchengine; }
	const SearchEngine& getSolver() const { return *searchengine; }
#ifdef CPSUPPORT
	CPSolver* cpsolver;
	bool hasCPSolver() const;
	CPSolver& getCPSolver() { return *cpsolver; }
	const CPSolver& getCPSolver() const { return *cpsolver; }
#endif

	EventQueue* queue;
	EventQueue& getEventQueue() { return *queue; }
	const EventQueue& getEventQueue() const { return *queue; }

	PropagatorFactory* factory;
	PropagatorFactory& getFactory() { return *factory; }
	const PropagatorFactory& getFactory() const { return *factory; }

	TheoryState state;

	std::vector<Propagator*> propagations;

	virtual void	notifyNonDecisionVar(Var var);

	// Explanation dummies: used to fix up learned clauses which are too small
	Var dummy1, dummy2;

	// OPTIMIZATION INFORMATION
	Optim 		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	// State saving
	int 				state_savedlevel;
	bool 				state_savingclauses;
	std::vector<rClause> state_savedclauses;

	// Logging
	SearchMonitor* searchmonitor;
	SearchMonitor& getSearchMonitor() { return *searchmonitor; }
	const SearchMonitor& getSearchMonitor() const { return *searchmonitor; }

public:
	PCSolver(SolverOption modes, MinisatID::WrapperPimpl& inter, int ID);
	virtual ~PCSolver();

	SearchEngine*	getSATSolver() const { return searchengine; }
#ifdef CPSUPPORT
	CPSolver* 		getCPSolverp() const { return cpsolver; }
#endif

	void		accept(Propagator* propagator);
	void 		accept(Watch* watch);
	void		acceptForBacktrack(Propagator* propagator);
	void		acceptForPropagation(Propagator* propagator);
	void 		accept(Propagator* propagator, EVENT event);
	void 		acceptBounds(IntVar* var, Propagator* propagator);
	void 		acceptLitEvent(Propagator* propagator, const Lit& lit, PRIORITY priority);
	void 		acceptFinishParsing(Propagator* propagator, bool late);

	void 		setModSolver(ModSolver* m);

	Var			newVar();
	int			newSetID();

	void 		finishParsing(bool& unsat);

	// Solving support
	void 		newDecisionLevel();
	bool 		solve			(const vec<Lit>& assumptions, const ModelExpandOptions& options);
	rClause 	checkFullAssignment();

	Var			changeBranchChoice(const Var& chosenvar);

	bool 		assertedBefore	(const Var& l, const Var& p) const;
	rClause		getExplanation	(const Lit& l);			//NON-OWNING pointer

	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	rClause 	createClause	(const vec<Lit>& lits, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void 		addLearnedClause(rClause c); 		//Propagate if clause is unit, return false if c is conflicting
	void 		removeClause	(rClause c);
	int			getClauseSize	(rClause cr) const;
	Lit			getClauseLit	(rClause cr, int i) const;
	void    	backtrackTo		(int level);		// Backtrack until a certain level.
	void    	setTrue			(const Lit& p, Propagator* solver, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined

	void 		notifySetTrue	(const Lit& p);

	const vec<Lit>& getTrail	() 		const;
	int 		getStartLastLevel() 	const;
	int 		getLevel		(int var) const; // Returns the decision level at which a variable was deduced.
	int			getCurrentDecisionLevel	() const;
	int			getNbDecisions	() 		const;
	std::vector<Lit> getDecisions() 	const;

	bool		isAlreadyUsedInAnalyze(const Lit& lit) const;

	bool 		totalModelFound	(); //cannot be const!

	void		varBumpActivity	(Var v);

	void 		backtrackDecisionLevel(int untillevel, const Lit& decision);
	rClause 	propagate		();

	void		notifyBoundsChanged(IntVar* var);

	void 		notifyClauseAdded(rClause clauseID);
	void 		notifyClauseDeleted(rClause clauseID);
	bool 		symmetryPropagationOnAnalyze(const Lit& p);

	int			getNbOfFormulas	() const;

	// MOD SOLVER support
	void		saveState		();
	void		resetState		();

	template<typename T>
	bool 		add(const T& sentence){ return getFactory().add(sentence); }
	void		createVar(Var v);

	void		addOptimization(Optim type, Var head);
	void		addOptimization(Optim type, const vec<Lit>& literals);

	// DEBUG
	void 		printEnqueued	(const Lit& p) const;
	void		printChoiceMade	(int level, Lit l) const;
	void 		printStatistics	() const;
	void		printState		() const;
	void		printClause		(rClause clause) const;
	void 		printCurrentOptimum(const Weight& value) const;

private:
	int 		getNbModelsFound() const;

	bool		isInitialized	() 	const { return state==THEORY_INITIALIZED; }
	bool		isInitializing	() 	const { return state==THEORY_INITIALIZING; }
	bool		isParsing		()	const { return state==THEORY_PARSING; }

	void 		extractLitModel(InnerModel* fullmodel);
	void 		extractVarModel(InnerModel* fullmodel);

	// SOLVING
	bool 		findNext		(const vec<Lit>& assumpts, const ModelExpandOptions& options);
	bool    	invalidateModel	(InnerDisjunction& clause);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(InnerDisjunction& clause);

	// OPTIMIZATION
    bool 		invalidateValue	(vec<Lit>& invalidation);
	bool 		invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 		findOptimal		(const vec<Lit>& assumps, const ModelExpandOptions& options);
};

}

#endif /* PCSOLVER_H_ */
