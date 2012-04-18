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

#include "external/LiteralPrinter.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "datastructures/OptimStatement.hpp"

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

class Monitor;

class PCSolver: public LiteralPrinter{
public:
	PCSolver(SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer, bool oneshot);
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
	bool parsingfinished, optimproblem;
	std::vector<OptimStatement> optimization;
public:
	void addOptimization(OptimStatement optim) {
		if(parsingfinished){
			throw idpexception("Cannot add additional optimizations after finishParsing has been called.");
		}
		optimization.push_back(optim);
		notifyOptimizationProblem();
	}

	// NOTE: only call from code which simplifies optimization statements
	void notifyOptimizationProblem(){
		optimproblem = true;
	}

	bool isOptimizationProblem() const {
		return optimproblem;
	}
	bool isAlwaysAtOptimum() const{
		return isOptimizationProblem() && optimization.size()==0;
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
	// NOTE: bypasses propagatorfactory, might be important for some actions!
	rClause createClause(const Disjunction& clause, bool learned);

	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void addLearnedClause(rClause c); //Propagate if clause is unit, return false if c is conflicting
	int getClauseSize(rClause cr) const;
	Lit getClauseLit(rClause cr, int i) const;

	// State saving
private:
	bool saved;
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

	int getNbOfFormulas() const;
};

}

#endif /* PCSOLVER_H_ */
