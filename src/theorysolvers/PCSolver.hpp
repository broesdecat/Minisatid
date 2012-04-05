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
class Printer;
typedef Minisat::Solver SearchEngine;

enum class Optim {
	LIST, SUBSET, AGG, VAR
};

struct OptimStatement{
	unsigned int priority; // Lower is earlier
	Optim optim;
	std::vector<Lit> to_minimize;
	Agg* agg_to_minimize;
	IntVar* var;
	bool atoptimum;

	OptimStatement(uint priority, Optim optim, litlist minim): priority(priority), optim(optim), to_minimize(minim), agg_to_minimize(NULL), var(NULL), atoptimum(false){
		MAssert(optim==Optim::LIST || optim==Optim::SUBSET);
	}
	OptimStatement(uint priority, Agg* agg): priority(priority), optim(Optim::AGG), agg_to_minimize(agg), var(NULL), atoptimum(false){

	}
	OptimStatement(uint priority, IntVar* var): priority(priority), optim(Optim::VAR), agg_to_minimize(NULL), var(var), atoptimum(false){

	}
};

class Monitor;

class PCSolver: public LiteralPrinter{
public:
	PCSolver(SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer);
	virtual ~PCSolver();

	// Options
private:
	SolverOption _modes;
public:
	int verbosity() const {
		return modes().verbosity;
	}
	const SolverOption& modes() const {
		return _modes;
	}

	// Var information
private:
	VarCreation* varcreator;
public:
	Var newVar();
private:
	void createVar(Var v, VARHEUR decide);
public:
	void notifyVarAdded();
	void varBumpActivity(Var v);
	void varReduceActivity(Var v);
	lbool value(Var x) const; // The current value of a variable.
	lbool value(Lit p) const; // The current value of a literal.
	lbool rootValue(Lit p) const; // The current value of a literal if it is known at level 0, otherwise l_Undef
	uint64_t nVars() const; // The current number of variables.
	int newSetID();

	// Decision information
public:
	bool isDecisionVar(Var var);
	void notifyDecisionVar(Var var);
	void notifyNonDecisionVar(Var var);
	bool isDecided(Var var);
	int getNbDecisions() const;
	std::vector<Lit> getDecisions() const;

	// Level information
public:
	int getStartLastLevel() const;
	int getLevel(int var) const; // Returns the decision level at which a variable was deduced.
	int getCurrentDecisionLevel() const;

	// Propagation and backtrack monitor
private:
	Monitor* monitor;

	// Optimization
public:
	// TODO prevent adding optimizations after parsing is done a first time.
	std::vector<OptimStatement> optimization;

	void addOptimization(OptimStatement optim){
		optimization.push_back(optim);
	}

	bool isOptimizationProblem() const {
		return optimization.size()>0;
	}

	OptimStatement& getCurrentOptim(){
		MAssert(optimization.size()==1);
		return optimization.front();
	}

	// Search
private:
	SearchEngine* searchengine;
	SearchEngine& getSolver() {
		return *searchengine;
	}
	const SearchEngine& getSolver() const {
		return *searchengine;
	}
public:
	SearchEngine* getSATSolver() const {
		return searchengine;
	}

	// CP-support
private:
	CPSolver* cpsolver;
public:
	bool hasCPSolver() const;
	CPSolver* getCPSolverp() const {return cpsolver;}
	const CPSolver& getCPSolver() const {return *cpsolver;}
	CPSolver& getCPSolver() {return *cpsolver;}
	rClause findNextCPModel();

	// Propagatorfactory
private:
	PropagatorFactory* factory;
	PropagatorFactory& getFactory() {
		return *factory;
	}
	const PropagatorFactory& getFactory() const {
		return *factory;
	}

	// Trail
private:
	TimeTrail* trail;
	std::vector<Propagator*> propagations;
public:
	const std::vector<Lit>& getTrail() const;

	// State
private:

	// Explanation dummies: used to fix up learned clauses which are too small
	Var dummy1, dummy2;

	// Termination management
private:
	bool terminate;
public:
	void notifyTerminateRequested();
	bool terminateRequested() const;

// Search management
public:
	/**
	 * Return true iff a model has been found
	 * Returns false iff unsat has been found
	 * Unknown otherwise (e.g. terminated)
	 */
	lbool solve(const litlist& assumptions, bool search);
	void finishParsing();
	void setTrue(const Lit& p, Propagator* solver, rClause c = nullPtrClause); // Enqueue a literal. Assumes value of literal is undefined
	void notifySetTrue(const Lit& p);
	void newDecisionLevel();
	void backtrackTo(int level); // Backtrack until a certain level.
	void backtrackDecisionLevel(int untillevel, const Lit& decision);
	rClause propagate();
	int getTime(const Var& var) const;
	bool assertedBefore(const Var& l, const Var& p) const;
	rClause getExplanation(const Lit& l); //NON-OWNING pointer
	bool isAlreadyUsedInAnalyze(const Lit& lit) const;
	void 	notifyBecameDecidable(Var v);
	void notifyBoundsChanged(IntVar* var);
	rClause notifyFullAssignmentFound();

	// Clause management
public:
	rClause createClause(const Disjunction& clause, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void addLearnedClause(rClause c); //Propagate if clause is unit, return false if c is conflicting
	int getClauseSize(rClause cr) const;
	Lit getClauseLit(rClause cr, int i) const;

	// State saving
public:
	void saveState();
	void resetState();

	// SATState information
public:
	void notifyUnsat();
	SATVAL satState() const;
	bool isUnsat() const {
		return satState() == SATVAL::UNSAT;
	}

	// Print information
private:
	LiteralPrinter* printer;
public:
	std::string toString(const Lit& lit) const;
	void printEnqueued(const Lit& p) const;
	void printChoiceMade(int level, const Lit& l) const;
	void printClause(rClause clause) const;

	// Model information
public:
	void extractLitModel(std::shared_ptr<Model> fullmodel);
	void extractVarModel(std::shared_ptr<Model> fullmodel);
	std::shared_ptr<Model> getModel();
	lbool getModelValue(Var v);

	// Constraint visiting
	void accept(ConstraintVisitor& visitor);

	// Queueing
private:
	EventQueue* queue;
	EventQueue& getEventQueue() {
		return *queue;
	}
	const EventQueue& getEventQueue() const {
		return *queue;
	}
public:
	void accept(Propagator* propagator);
	void accept(GenWatch* const watch);
	void acceptForBacktrack(Propagator* propagator);
	void acceptForPropagation(Propagator* propagator);
	void accept(Propagator* propagator, EVENT event);
	void acceptBounds(IntView* var, Propagator* propagator);
	void accept(Propagator* propagator, const Lit& lit, PRIORITY priority);
	void acceptForDecidable(Var v, Propagator* prop);

private:
	// If lazy, do not decide for literals in decisions
	// NOTE: only use this if the watches mechanism of the constraint will take care of making literal decidable if necessary
	VARHEUR lazyDecide() const;
	void addVars		(const std::vector<Var>& vars, VARHEUR heur = VARHEUR::DECIDE);
public:
	template<typename T>
	void add(const T& obj){
		addVars(obj.getAtoms(), lazyDecide());
		getFactory().add(obj);
	}
};

}

#endif /* PCSOLVER_H_ */
