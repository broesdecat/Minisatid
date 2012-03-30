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
#include <memory>

#include "constraintvisitors/LiteralPrinter.hpp"
#include "theorysolvers/PropagatorFactory.hpp"

namespace Minisat {
class Solver;
}

namespace MinisatID {

class TimeTrail;
class CPSolver;
class SolverOption;
class Propagator;
class PropagatorFactory;
class EventQueue;
class SearchMonitor;
class IntView;
class VarCreation;
class ConstraintVisitor;
typedef Minisat::Solver SearchEngine;

enum TheoryState {
	THEORY_PARSING, THEORY_INITIALIZED, THEORY_INITIALIZING
};

class InnerMonitor;

class PCSolver: public LiteralPrinter{
private:
	SolverOption _modes;

	VarCreation* varcreator;
	InnerMonitor* monitor;

public:
	int verbosity() const {
		return modes().verbosity;
	}
	const SolverOption& modes() const {
		return _modes;
	}
	SolverOption& getNonConstOptions() {
		return _modes;
	}
	void setVerbosity(int verb) {
		_modes.verbosity = verb;
	}
	void setNbModels(int nbmodels) {
		_modes.nbmodels = nbmodels;
	}
public:
	// FIXME make private with getters!
	// OPTIMIZATION INFORMATION
	Optim optim;
	Var head;
	std::vector<Lit> to_minimize;
	Agg* agg_to_minimize;

	void addOptimization(Optim type, const litlist& literals);
	void addAggOptimization(Agg* aggmnmz);

	bool isOptimizationProblem() const {
		return optim!=Optim::NONE;
	}

private:
	//Search algorithms //TODO refactor into an interface "searchalgorithm" with subclasses satsolver and cpsolver?
	SearchEngine* searchengine;
	SearchEngine& getSolver() {
		return *searchengine;
	}
	const SearchEngine& getSolver() const {
		return *searchengine;
	}
#ifdef CPSUPPORT
	CPSolver* cpsolver;
	bool hasCPSolver() const;
	CPSolver& getCPSolver() {return *cpsolver;}
	const CPSolver& getCPSolver() const {return *cpsolver;}
#endif

	EventQueue* queue;
	EventQueue& getEventQueue() {
		return *queue;
	}
	const EventQueue& getEventQueue() const {
		return *queue;
	}

	PropagatorFactory* factory;
	PropagatorFactory& getFactory() {
		return *factory;
	}
	const PropagatorFactory& getFactory() const {
		return *factory;
	}

	TheoryState state;

	// Explanation dummies: used to fix up learned clauses which are too small
	Var dummy1, dummy2;

	// Trail support
	TimeTrail* trail;
	std::vector<Propagator*> propagations;

	// State saving
	int state_savedlevel;
	bool state_savingclauses;
	std::vector<rClause> state_savedclauses;

public:
	PCSolver(SolverOption modes);
	virtual ~PCSolver();

	SearchEngine* getSATSolver() const {
		return searchengine;
	}
#ifdef CPSUPPORT
	CPSolver* getCPSolverp() const {return cpsolver;}
#endif

	bool terminate;
	void notifyTerminateRequested();
	bool terminateRequested() const;

	const std::vector<Lit>& getTrail() const;

	void preventPropagation();
	void allowPropagation();

	bool isDecisionVar(Var var);
	void notifyDecisionVar(Var var);
	void notifyNonDecisionVar(Var var);

	void accept(Propagator* propagator);
	void accept(GenWatch* const watch);
	void acceptForBacktrack(Propagator* propagator);
	void acceptForPropagation(Propagator* propagator);
	void accept(Propagator* propagator, EVENT event);
	void acceptBounds(IntView* var, Propagator* propagator);
	void accept(Propagator* propagator, const Lit& lit, PRIORITY priority);
	void acceptFinishParsing(Propagator* propagator, bool late);

	void acceptForDecidable(Var v, Propagator* prop);
	void notifyBecameDecidable(Var v);

	Var newVar();
	int newSetID();

	void finishParsing();

	std::string printLiteral(const Lit& lit) const;

	/**
	 * Return true iff a model has been found
	 * Returns false iff unsat has been found
	 * Unknown otherwise (e.g. terminated)
	 */
	lbool solve(const litlist& assumptions, bool search);

	void setTrue(const Lit& p, Propagator* solver, rClause c = nullPtrClause); // Enqueue a literal. Assumes value of literal is undefined
	void notifySetTrue(const Lit& p);
	void newDecisionLevel();
	rClause checkFullAssignment();
	bool hasTotalModel(); //cannot be const!
	void backtrackTo(int level); // Backtrack until a certain level.
	void backtrackDecisionLevel(int untillevel, const Lit& decision);
	rClause propagate();

	bool isDecided(Var var);

	int getTime(const Var& var) const;
	bool assertedBefore(const Var& l, const Var& p) const;
	rClause getExplanation(const Lit& l); //NON-OWNING pointer
	bool isAlreadyUsedInAnalyze(const Lit& lit) const;

	void varBumpActivity(Var v);
	void varReduceActivity(Var v);
	lbool value(Var x) const; // The current value of a variable.
	lbool value(Lit p) const; // The current value of a literal.
	uint64_t nVars() const; // The current number of variables.

	rClause createClause(const InnerDisjunction& clause, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void addLearnedClause(rClause c); //Propagate if clause is unit, return false if c is conflicting
	void removeClause(rClause c);
	int getClauseSize(rClause cr) const;
	Lit getClauseLit(rClause cr, int i) const;

	int getStartLastLevel() const;
	int getLevel(int var) const; // Returns the decision level at which a variable was deduced.
	int getCurrentDecisionLevel() const;
	int getNbDecisions() const;
	std::vector<Lit> getDecisions() const;

	bool handleConflict(rClause conflict);

	void notifyBoundsChanged(IntVar* var);

	// MOD SOLVER support
	void saveState();
	void resetState();

	template<typename T>
	void add(const T& sentence) {
		getFactory().add(sentence);
	}
	void createVar(Var v, VARHEUR decide);
	void notifyVarAdded();

	SATVAL satState() const;
	void notifyUnsat();
	bool isUnsat() const {
		return satState() == SATVAL::UNSAT;
	}

	// DEBUG
	void printEnqueued(const Lit& p) const;
	void printChoiceMade(int level, const Lit& l) const;
	void printClause(rClause clause) const;

	void extractLitModel(std::shared_ptr<InnerModel> fullmodel);
	void extractVarModel(std::shared_ptr<InnerModel> fullmodel);

	std::shared_ptr<InnerModel> getModel();
	lbool getModelValue(Var v);

	void accept(ConstraintVisitor& visitor);
};

}

#endif /* PCSOLVER_H_ */
