/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include "utils/Utils.hpp"
#include <memory>

#include "external/LiteralPrinter.hpp"
#include "external/MXStatistics.hpp"
#include "theorysolvers/TheorySimplifier.hpp"
#include "datastructures/OptimStatement.hpp"

namespace Minisat {
class Solver;
}

namespace MinisatID {

class TimeTrail;
class SolverOption;
class Propagator;
class EventQueue;
class IntView;
class VarCreation;
class ConstraintVisitor;
class Printer;
class MinisatHeuristic;

class Monitor;

class PCSolver: public LiteralPrinter{
private:
	TheoryID theoryID;
public:
	PCSolver(TheoryID theoryID, SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer, bool oneshot);
	virtual ~PCSolver();

	TheoryID getTheoryID() const{
		return theoryID;
	}

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
	VarID newID();
	Atom newAtom();
	void createVar(Atom v, TheoryID theoryID);
	IntView* getIntView(VarID id, Weight bound);

	MinisatHeuristic& getHeuristic();
	void notifyHeuristicOfLazyAtom(Atom v, Atom v1, Atom v2);


	// NOTE: do not pass around indiscriminately! Does not pass on ownership
	VarCreation* getVarCreator() const { return varcreator; }

public:
	lbool value(Lit p) const; // The current value of a literal.
	lbool rootValue(Lit p) const; // The current value of a literal if it is known at level 0, otherwise l_Undef
	uint64_t nVars() const; // The current number of variables.
	int newSetID(){
		return minnewset--;
	}

	// Decision information
private:
	bool _outputvarsset;
	std::set<Atom> _outputvars;
	std::set<VarID> _outputvarids;
public:
	void addOutputVarId(const VarID& vid);
	bool isOutputVarId(const VarID& vid);
	void addOutputVars(const std::vector<Atom>& outputvars);
	bool isDecisionVar(Atom var); // This is confusing, seems to have the same functionality as "isDecided". Rename to canBeDecisionVar or allowedAsDecisionVar?
	void notifyDecisionVar(Atom var);
	bool isDecided(Atom var);
	std::vector<Lit> getDecisions() const;
	void invalidate(litlist& clause) const;
	bool moreModelsPossible() const;
	bool isTwoValued() const;

	// Level information
public:
	int getLevel(int var) const; // Returns the decision level at which a variable was deduced.
	int getCurrentDecisionLevel() const;

	// Propagation and backtrack monitor
private:
	bool hasMonitors() const;
	Monitor* monitor;

	bool parsingfinished, needNewFinishCall;

	// Optimization
	bool optimproblem;
	std::vector<OptimStatement> optimization;
public:
	void addOptimization(OptimStatement optim) {
		if(parsingfinished){
			throw idpexception("Cannot add additional optimizations after finishParsing has been called.");
		}
		optimization.push_back(optim);
	}

	// Note: only call after finishparsing!
	bool isOptimizationProblem() const {
		return optimization.size()>0;
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

	// Propagatorfactory
private:
	Factory* factory;
	const Factory& getFactory() const {
		return *factory;
	}
	Factory& getFactory() {
		return *factory;
	}
public:
	Factory& getFactory(TheoryID id) {
		if(id!=getTheoryID()){
			throw idpexception("Invalid code path");
		}
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
	Atom dummy1, dummy2;
	int minnewset; // Internal sets count downwards!

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
  void addAssumption(const Lit assump);
  void removeAssumption(const Lit assump);
  void clearAssumptions();

	/**
	 * Return true iff a model has been found
	 * Returns false iff unsat has been found
	 * Unknown otherwise (e.g. terminated)
	 */
	lbool solve(bool search);

	litlist getUnsatExplanation() const;
	void finishParsing();
	void setTrue(const Lit& p, Propagator* solver, rClause c = nullPtrClause); // Enqueue a literal. Assumes value of literal is undefined
	void notifySetTrue(const Lit& p);
	void newDecisionLevel();
	void backtrackTo(int level); // Backtrack until a certain level.
	void backtrackDecisionLevel(int untillevel, const Lit& decision);
	rClause propagate();
	int getTime(const Atom& var) const;
	bool assertedBefore(const Atom& l, const Atom& p) const;
	rClause getExplanation(const Lit& l); //NON-OWNING pointer // JO: is this pointer owning or non-owning?? .cpp says it is.
	bool isAlreadyUsedInAnalyze(const Lit& lit) const;
	void notifyBecameDecidable(Atom v);
	void notifyBoundsChanged(IntVar* var);
	rClause notifyFullAssignmentFound();

	// Called by lazy grounding to do finishparsing if real parsing has already been finished.
	// Finishparsing among others guarantees that propagators for definitions are created / updated
	void notifyFinishParsingNeed();

	// Clause management
public:
	// NOTE: bypasses propagatorfactory, might be important for some actions!
	rClause createClause(const Disjunction& clause, bool learned);

	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void addLearnedClause(rClause c); //Cannot be conflicting!
	void addConflictClause(rClause c); //Needs to be conflicting! Do not handle that conflict at this time!
	int getClauseSize(rClause cr) const;
	Lit getClauseLit(rClause cr, int i) const;

  void getOutOfUnsat();

	// SATState information
	void notifyUnsat();
	SATVAL satState() const;
	bool isUnsat() const {
		return satState() == SATVAL::UNSAT;
	}

	// Print information
private:
	LiteralPrinter* printer;
public:
	bool isTseitin(const Atom& atom) const;
	virtual void setString(const Atom& lit, const std::string& name);
	virtual std::string toString(VarID id) const;
	virtual std::string toString(const Lit& lit) const;
	void printEnqueued(const Lit& p) const;
	void printChoiceMade(int level, const Lit& l) const;
	void printClause(rClause clause) const;

	// Model information
public:
	void extractLitModel(std::shared_ptr<Model> fullmodel);
	void extractVarModel(std::shared_ptr<Model> fullmodel);
	std::shared_ptr<Model> getModel();
	lbool getModelValue(Atom v);
	lbool getModelValue(const Lit& lit);
	litlist getEntailedLiterals() const;
	MXStatistics getStats() const;

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
	// IMPORTANT: EACH PROPAGATOR SHOULD DO THIS ONLY ONCE!!!
	void accept(Propagator* propagator);

	void accept(GenWatch* const watch);
	void acceptForPropagation(Propagator* propagator, PRIORITY priority = PRIORITY::FASTEST);
	void accept(Propagator* propagator, EVENT event);
	void acceptBounds(IntView* var, Propagator* propagator);
	void accept(Propagator* propagator, const Lit& lit, PRIORITY priority);
	void acceptForDecidable(Atom v, Propagator* prop);

	int getNbOfFormulas() const;

public:
	Lit getLit(VarID var, EqType eq, Weight bound);

private:
	long groundingCalls, maxCallsBeforeRestart;
public:
	void notifyGroundingCall();
};

}
