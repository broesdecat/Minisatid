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

class TimeTrail;
class CPSolver;
class ModSolver;
class SolverOption;
class Propagator;
class PropagatorFactory;
class EventQueue;
class SearchMonitor;
class IntView;
typedef Minisat::Solver SearchEngine;

enum class Optim { LIST, SUBSET, AGG, NONE };

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

	// Explanation dummies: used to fix up learned clauses which are too small
	Var dummy1, dummy2;

	// Trail support
	TimeTrail* trail;
	std::vector<Propagator*> propagations;

	// OPTIMIZATION INFORMATION
	Optim 		optim;
	Var 		head;
	litlist		to_minimize;
	Agg*		agg_to_minimize;

	// State saving
	int 				state_savedlevel;
	bool 				state_savingclauses;
	std::vector<rClause> state_savedclauses;

public:
	PCSolver(SolverOption modes, MinisatID::WrapperPimpl& inter, int ID);
	virtual ~PCSolver();

	SearchEngine*	getSATSolver() const { return searchengine; }
#ifdef CPSUPPORT
	CPSolver* 		getCPSolverp() const { return cpsolver; }
#endif

	bool		isDecisionVar(Var var);
	void		notifyDecisionVar(Var var);
	void		notifyNonDecisionVar(Var var);

	void		accept(Propagator* propagator);
	void 		accept(GenWatch* const watch);
	void		acceptForBacktrack(Propagator* propagator);
	void		acceptForPropagation(Propagator* propagator);
	void 		accept(Propagator* propagator, EVENT event);
	void 		acceptBounds(IntView* var, Propagator* propagator);
	void 		accept(Propagator* propagator, const Lit& lit, PRIORITY priority);
	void 		acceptFinishParsing(Propagator* propagator, bool late);

	Var			newVar();
	int			newSetID();

	void 		finishParsing(bool& unsat);

	void    	setTrue			(const Lit& p, Propagator* solver, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined
	void 		notifySetTrue	(const Lit& p);
	void 		newDecisionLevel();
	bool 		solve			(const litlist& assumptions, const ModelExpandOptions& options);
	rClause 	checkFullAssignment();
	bool 		hasTotalModel(); //cannot be const!
	void    	backtrackTo		(int level);		// Backtrack until a certain level.
	void 		backtrackDecisionLevel(int untillevel, const Lit& decision);
	rClause 	propagate		();

	Var			changeBranchChoice(const Var& chosenvar);

	int			getTime(const Var& var) const;
	bool 		assertedBefore	(const Var& l, const Var& p) const;
	rClause		getExplanation	(const Lit& l);			//NON-OWNING pointer
	bool		isAlreadyUsedInAnalyze(const Lit& lit) const;

	void		varBumpActivity	(Var v);
	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	rClause 	createClause	(const InnerDisjunction& clause, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void 		addLearnedClause(rClause c); 		//Propagate if clause is unit, return false if c is conflicting
	void 		removeClause	(rClause c);
	int			getClauseSize	(rClause cr) const;
	Lit			getClauseLit	(rClause cr, int i) const;

	int 		getStartLastLevel() 	const;
	int 		getLevel		(int var) const; // Returns the decision level at which a variable was deduced.
	int			getCurrentDecisionLevel	() const;
	int			getNbDecisions	() 		const;
	std::vector<Lit> getDecisions() 	const;


	void		notifyBoundsChanged(IntVar* var);

	void 		notifyClauseAdded(rClause clauseID);
	bool 		symmetryPropagationOnAnalyze(const Lit& p);

	int			getNbOfFormulas	() const;

	bool 		propagateSymmetry(const Lit& l);
	bool		propagateSymmetry2();

	// MOD SOLVER support
	void 		setModSolver(ModSolver* m);
	void		saveState		();
	void		resetState		();

	template<typename T>
	void 		add(const T& sentence){ getFactory().add(sentence); }
	void		createVar(Var v, bool nondecision = false);

	SATVAL 		satState() const;
	void		notifyUnsat();

	void		addOptimization(Optim type, const litlist& literals);
	void 		addAggOptimization(TypedSet* aggmnmz);

	void 		printTheory(std::ostream& stream);

	// DEBUG
	void 		printEnqueued	(const Lit& p) const;
	void		printChoiceMade	(int level, Lit l) const;
	void 		printStatistics	() const;
	void		printState		() const;
	void		printClause		(rClause clause) const;
	void 		printCurrentOptimum(const Weight& value) const;

	bool		isInitialized	() 	const { return state==THEORY_INITIALIZED; }

private:
	int 		getNbModelsFound() const;

	bool		isInitializing	() 	const { return state==THEORY_INITIALIZING; }
	bool		isParsing		()	const { return state==THEORY_PARSING; }

	void 		extractLitModel(InnerModel* fullmodel);
	void 		extractVarModel(InnerModel* fullmodel);

	// SOLVING
	bool 		findNext		(const Minisat::vec<Lit>& assumpts, const ModelExpandOptions& options);
	SATVAL    	invalidateModel	(InnerDisjunction& clause);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(InnerDisjunction& clause);

	// OPTIMIZATION
    bool 		invalidateValue	(litlist& invalidation);
	bool 		invalidateSubset(litlist& invalidation, Minisat::vec<Lit>& assmpt);
	bool 		invalidateAgg	(litlist& invalidation);
	bool 		findOptimal		(const litlist& assumps, const ModelExpandOptions& options);
};

}

#endif /* PCSOLVER_H_ */
