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

enum class Optim {
	LIST, SUBSET, AGG, VAR
};

struct OptimStatement {
	unsigned int priority; // Lower is earlier
	Optim optim;
	std::vector<Lit> to_minimize;
	Agg* agg_to_minimize;
	IntVar* var;
	bool atoptimum;

	OptimStatement(uint priority, Optim optim, litlist minim) :
			priority(priority), optim(optim), to_minimize(minim), agg_to_minimize(NULL), var(NULL), atoptimum(false) {
		MAssert(optim==Optim::LIST || optim==Optim::SUBSET);
	}
	OptimStatement(uint priority, Agg* agg) :
			priority(priority), optim(Optim::AGG), agg_to_minimize(agg), var(NULL), atoptimum(false) {

	}
	OptimStatement(uint priority, IntVar* var) :
			priority(priority), optim(Optim::VAR), agg_to_minimize(NULL), var(var), atoptimum(false) {

	}
};

class Monitor;

class ConstraintDatabase: public LiteralPrinter{
public:
	virtual ~ConstraintDatabase() {}

	virtual PropagatorFactory& getFactory() = 0;
	virtual void createVar(Var v) = 0;
};

class BothPCSolver: public ConstraintDatabase {
public:
	virtual int verbosity() const = 0;
	virtual const SolverOption& modes() const = 0;
	virtual Var newVar() = 0;
	virtual int newSetID() = 0;
	virtual lbool rootValue(Lit p) const = 0;
	virtual Lit getTrueLit() const = 0;
	virtual Lit getFalseLit() const = 0;

	virtual void notifyUnsat() = 0;
	virtual SATVAL satState() const = 0;
	virtual bool isUnsat() const = 0;
	virtual std::string toString(const Lit& lit) const = 0;

	virtual void invalidate(litlist& clause) const = 0;

	virtual void backtrackTo(int level) = 0;
};

class SearchEngine: virtual public BothPCSolver {
public:
	virtual void finishParsing() = 0;
	virtual bool isOptimizationProblem() const = 0;
	virtual bool hasNextOptimum() const = 0;
	virtual OptimStatement& getNextOptimum() = 0;

	virtual bool hasCPSolver() const = 0;
	virtual SATVAL findNextCPModel() = 0;

	virtual void notifyTerminateRequested() = 0;

	virtual void saveState() = 0;
	virtual void resetState() = 0;

	virtual void extractLitModel(std::shared_ptr<Model> fullmodel) = 0;
	virtual void extractVarModel(std::shared_ptr<Model> fullmodel) = 0;
	virtual std::shared_ptr<Model> getModel() = 0;
	virtual lbool getModelValue(Var v) = 0;

	virtual void accept(ConstraintVisitor& visitor) = 0;

	virtual void setAssumptions(const litlist& assumps) = 0;
	virtual lbool solve(bool search) = 0;

	virtual litlist getEntailedLiterals() const = 0;
	virtual bool moreModelsPossible() const = 0;
};

class PCSolver: virtual public BothPCSolver {
public:
	virtual int getCurrentDecisionLevel() const = 0;

	virtual void varBumpActivity(Var v) = 0;
	virtual void varReduceActivity(Var v) = 0;
	virtual lbool value(Lit p) const = 0;
	virtual uint64_t nVars() const = 0;
	virtual bool isDecisionVar(Var var) = 0;
	virtual void notifyDecisionVar(Var var) = 0;
	virtual bool isDecided(Var var) = 0;
	virtual int getLevel(int var) const = 0;
	virtual void addOptimization(OptimStatement optim) = 0;
	virtual SATSolver* getSATSolver() const = 0;
	virtual CPSolver* getCPSolver() const = 0;
	virtual const std::vector<Lit>& getTrail() const = 0;
	virtual bool terminateRequested() const = 0;

	virtual rClause createClause(const Disjunction& clause, bool learned) = 0;
	virtual void addLearnedClause(rClause c) = 0;
	virtual int getClauseSize(rClause cr) const = 0;
	virtual Lit getClauseLit(rClause cr, int i) const = 0;
	virtual void printEnqueued(const Lit& p) const = 0;
	virtual void printChoiceMade(int level, const Lit& l) const = 0;
	virtual void printClause(rClause clause) const = 0;

	virtual void accept(Propagator* propagator) = 0;
	virtual void accept(GenWatch* const watch) = 0;
	virtual void acceptForBacktrack(Propagator* propagator) = 0;
	virtual void acceptForPropagation(Propagator* propagator) = 0;
	virtual void accept(Propagator* propagator, EVENT event) = 0;
	virtual void acceptBounds(IntView* var, Propagator* propagator) = 0;
	virtual void accept(Propagator* propagator, const Lit& lit, PRIORITY priority) = 0;
	virtual void acceptForDecidable(Var v, Propagator* prop) = 0;

	virtual void finishParsing() = 0;
	virtual void setTrue(const Lit& p, Propagator* solver, rClause c = nullPtrClause) = 0;
	virtual void notifySetTrue(const Lit& p) = 0;
	virtual void newDecisionLevel() = 0;
	virtual void backtrackDecisionLevel(int untillevel, const Lit& decision) = 0;
	virtual rClause propagate() = 0;
	virtual int getTime(const Var& var) const = 0;
	virtual bool assertedBefore(const Var& l, const Var& p) const = 0;
	virtual rClause getExplanation(const Lit& l) = 0;
	virtual bool isAlreadyUsedInAnalyze(const Lit& lit) const = 0;
	virtual void notifyBecameDecidable(Var v) = 0;
	virtual void notifyBoundsChanged(IntVar* var) = 0;
	virtual rClause notifyFullAssignmentFound() = 0;
};

class PCSolverImpl: public PCSolver, public SearchEngine {
public:
	PCSolverImpl(SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer, bool oneshot);
	virtual ~PCSolverImpl();

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
	void createVar(Var v);
public:
	void varBumpActivity(Var v);
	void varReduceActivity(Var v);
	lbool value(Lit p) const; // The current value of a literal.
	lbool rootValue(Lit p) const; // The current value of a literal if it is known at level 0, otherwise l_Undef
	uint64_t nVars() const; // The current number of variables.
	int newSetID();

	// Decision information
public:
	bool isDecisionVar(Var var);
	void notifyDecisionVar(Var var);
	bool isDecided(Var var);
	std::vector<Lit> getDecisions() const;
	void invalidate(litlist& clause) const;
	bool moreModelsPossible() const;

	// Level information
public:
	int getLevel(int var) const; // Returns the decision level at which a variable was deduced.
	int getCurrentDecisionLevel() const;

	// Propagation and backtrack monitor
private:
	bool monitoring; // True if at time of solve() call, there are monitors (optimization!)
	Monitor* monitor;

	// Optimization
	std::vector<OptimStatement> optimization; // TODO prevent adding optimizations after parsing is done a first time.
public:
	void addOptimization(OptimStatement optim) {
		optimization.push_back(optim);
	}

	bool isOptimizationProblem() const {
		return optimization.size() > 0;
	}

	uint currentoptim;
	bool hasNextOptimum() const {
		MAssert(isOptimizationProblem());
		return currentoptim < optimization.size();
	}
	OptimStatement& getNextOptimum() {
		return optimization[currentoptim++];
	}

	// Search
private:
	SATSolver* searchengine;
	SATSolver& getSolver() {
		return *searchengine;
	}
	const SATSolver& getSolver() const {
		return *searchengine;
	}
public:
	SATSolver* getSATSolver() const {
		return searchengine;
	}

	// CP-support
private:
	CPSolver* cpsolver;
public:
	bool hasCPSolver() const;
	SATVAL findNextCPModel();
	CPSolver* getCPSolver() const {
		return cpsolver;
	}

	// Propagatorfactory
private:
	PropagatorFactory* factory;
	const PropagatorFactory& getFactory() const {
		return *factory;
	}
public:
	PropagatorFactory& getFactory() {
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
	Var dummy1, dummy2, dummyfalse;
public:
	Lit getTrueLit() const;
	Lit getFalseLit() const;

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
	void setAssumptions(const litlist& assumps);
	lbool solve(bool search);
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
	void notifyBecameDecidable(Var v);
	void notifyBoundsChanged(IntVar* var);
	rClause notifyFullAssignmentFound();

	// Clause management
public:
	// FIXME bypasses propagatorfactory, might be important for some actions!
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
	litlist getEntailedLiterals() const;

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
};

}

#endif /* PCSOLVER_H_ */
