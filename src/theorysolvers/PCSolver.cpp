/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "theorysolvers/PCSolver.hpp"

#include <iostream>
#include "satsolver/SATSolver.hpp"
#include "modules/cpsolver/CPSolver.hpp"
#include "modules/IntVar.hpp"

#include "theorysolvers/PropagatorFactory.hpp"
#include "theorysolvers/EventQueue.hpp"
#include "theorysolvers/TimeTrail.hpp"
#include "external/Space.hpp"
#include "datastructures/InternalAdd.hpp"

#include "modules/aggsolver/AggSet.hpp"
#include "constraintvisitors/ConstraintVisitor.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

using Minisat::vec;

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer, bool oneshot) :
		_modes(modes), varcreator(varcreator), monitor(monitor), monitoring(false), parsingfinished(false), optimproblem(false), currentoptim(0), searchengine(NULL),
#ifdef CPSUPPORT
				cpsolver(NULL),
#endif
				factory(NULL), trail(new TimeTrail()), terminate(false), saved(false), printer(printer), queue(NULL) {
	queue = new EventQueue(*this);
	searchengine = createSolver(this, oneshot);

#ifdef CPSUPPORT
	cpsolver = new CPSolver(this);
#endif

	factory = new PropagatorFactory(modes, this);

	if (verbosity() > 1) {
		modes.print(clog);
	}

	dummy1 = newVar();
	dummy2 = newVar();
	dummyfalse = newVar();
	add(Disjunction( { mkPosLit(dummy1) }), *this);
	add(Disjunction( { mkPosLit(dummy2) }), *this);
	add(Disjunction( { mkNegLit(dummyfalse) }), *this);
}

Lit PCSolver::getTrueLit() const {
	return mkPosLit(dummy1);
}
Lit PCSolver::getFalseLit() const {
	return mkPosLit(dummyfalse);
}

PCSolver::~PCSolver() {
	delete (queue);
	// NOTE: solvers are deleted by the queue!
	delete (factory);
	delete (trail);
}

bool PCSolver::hasCPSolver() const {
#ifdef CPSUPPORT
	return cpsolver!=NULL && cpsolver->isPresent();
#else
	return false;
#endif
}
SATVAL PCSolver::findNextCPModel() {
#ifdef CPSUPPORT
	MAssert(hasCPSolver());
	if(not getCPSolver()->hasData()) {
		return SATVAL::UNSAT;
	}
	return getCPSolver()->findNextModel()==nullPtrClause?SATVAL::POS_SAT:SATVAL::UNSAT;
#else
	throw idpexception("Calling methods on cpsolver while gecode is not compiled in.");
#endif
}

void PCSolver::invalidate(litlist& clause) const {
	// Add negation of model as clause for next iteration.
	// By default: by adding all choice literals
	auto v = getSolver().getDecisions();
	for (auto i = v.cbegin(); i < v.cend(); ++i) {
		clause.push_back(~(*i));
	}
}
bool PCSolver::moreModelsPossible() const {
	return getCurrentDecisionLevel() != getSolver().getNbOfAssumptions();
}

lbool PCSolver::value(Lit p) const {
	return getSolver().value(p);
}
lbool PCSolver::rootValue(Lit p) const {
	return getSolver().rootValue(p);
}
uint64_t PCSolver::nVars() const {
	return getSolver().nbVars();
}
void PCSolver::notifyTerminateRequested() {
	terminate = true;
}
bool PCSolver::terminateRequested() const {
	return terminate;
}

const std::vector<Lit>& PCSolver::getTrail() const {
	return trail->getTrail();
}

bool PCSolver::isDecisionVar(Var var) {
	if ((uint64_t) var >= nVars()) {
		return false;
	}
	return getSATSolver()->isDecisionVar(var);
}
void PCSolver::notifyDecisionVar(Var var) {
	getSATSolver()->setDecidable(var, true);
}

rClause PCSolver::createClause(const Disjunction& clause, bool learned) {
	if (clause.literals.size() == 0) {
		return getSolver().makeClause( { mkNegLit(dummy1), mkNegLit(dummy2) }, learned);
	} else if (clause.literals.size() == 1) {
		return getSolver().makeClause( { clause.literals[0], mkNegLit(dummy1) }, learned);
	} else {
		return getSolver().makeClause(clause.literals, learned);
	}
}

void PCSolver::acceptForDecidable(Var v, Propagator* prop) {
	getEventQueue().acceptForDecidable(v, prop);
}
void PCSolver::notifyBecameDecidable(Var v) {
	getEventQueue().notifyBecameDecidable(v);
}

void PCSolver::addLearnedClause(rClause c) {
	getSolver().addLearnedClause(c);
}
int PCSolver::getClauseSize(rClause cr) const {
	return getSolver().getClauseSize(cr);
}
Lit PCSolver::getClauseLit(rClause cr, int i) const {
	return getSolver().getClauseLit(cr, i);
}

void PCSolver::backtrackTo(int level) {
	getSolver().cancelUntil(level);
}

void PCSolver::setTrue(const Lit& p, Propagator* module, rClause c) {
	MAssert(module != NULL);
	MAssert(value(p)!=l_False && value(p)!=l_True);
	propagations[var(p)] = module;
	getSolver().uncheckedEnqueue(p, c);
}

void PCSolver::notifySetTrue(const Lit& p) {
	getEventQueue().setTrue(p);
	trail->notifyPropagate(p);

	if (monitoring) {
		monitor->notifyMonitor(p, getCurrentDecisionLevel());
	}
}

int PCSolver::getCurrentDecisionLevel() const {
	return getSolver().decisionLevel();
}

int PCSolver::getLevel(int var) const {
	return getSolver().getLevel(var);
}

vector<Lit> PCSolver::getDecisions() const {
	return getSolver().getDecisions();
}

bool PCSolver::isAlreadyUsedInAnalyze(const Lit& lit) const {
	return getSolver().isAlreadyUsedInAnalyze(lit);
}

void PCSolver::varBumpActivity(Var v) {
	getSolver().varBumpActivity(v);
}

void PCSolver::varReduceActivity(Var v) {
	getSolver().varReduceActivity(v);
}

void PCSolver::accept(Propagator* propagator) {
	getEventQueue().accept(propagator);
}

void PCSolver::accept(GenWatch* const watch) {
	getEventQueue().accept(watch);
}

void PCSolver::acceptForBacktrack(Propagator* propagator) {
	getEventQueue().acceptForBacktrack(propagator);
}
void PCSolver::acceptForPropagation(Propagator* propagator) {
	getEventQueue().acceptForPropagation(propagator);
}

void PCSolver::accept(Propagator* propagator, EVENT event) {
	getEventQueue().accept(propagator, event);
}

void PCSolver::acceptBounds(IntView* var, Propagator* propagator) {
	getEventQueue().acceptBounds(var, propagator);
}

void PCSolver::accept(Propagator* propagator, const Lit& lit, PRIORITY priority) {
	getEventQueue().accept(propagator, lit, priority);
}

Var PCSolver::newVar() {
	auto var = varcreator->createVar();
	if (var >= nVars()) {
		getEventQueue().notifyNbOfVars(var); // IMPORTANT to do it before effectively creating it in the solver (might trigger grounding)
	}
	createVar(var);
	return var;
}

/**
 * VARHEUR::DECIDE has precedence over NON_DECIDE for repeated calls to the same var!
 */
void PCSolver::createVar(Var v) {
	MAssert(v>-1);

	if (((uint64_t) v) >= nVars()) {
		getEventQueue().notifyNbOfVars(v + 1); // IMPORTANT to do it before effectively creating vars in the solver (might trigger grounding)
		while (((uint64_t) v) >= nVars()) {
			getSolver().newVar(modes().polarity == Polarity::TRUE ? l_True : modes().polarity == Polarity::FALSE ? l_False : l_Undef, false);
		}
	}

	if (not getSolver().isDecisionVar(v)) {
		// If lazy, do not decide for literals in decisions
		// NOTE: only use this if the watches mechanism of the constraint will take care of making literal decidable if necessary
		auto decide = modes().lazy ? VARHEUR::DONT_DECIDE : VARHEUR::DECIDE;
		getSolver().setDecidable(v, decide == VARHEUR::DECIDE);
		if (propagations.size() < nVars()) { //Lazy init
			propagations.resize(nVars(), NULL);
		}
	}
}

int PCSolver::newSetID() {
	return getFactory().newSetID();
}

void PCSolver::notifyBoundsChanged(IntVar* var) {
	getEventQueue().notifyBoundsChanged(var);
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(const Lit& l) {
	if (modes().verbosity > 2) {
		clog << "Generating explanation for " << toString(l) << ", ";
	}

	auto propagator = propagations[var(l)];
	if(propagator == NULL){
		auto res= getSolver().reason(var(l));
		MAssert(res != nullPtrClause);
		return res;
	}
	MAssert(propagator!=NULL);
	//If this happens, there is usually an error in the generated explanations!

	if (modes().verbosity > 2) {
		clog << "Generated by " << propagator->getName() << ": ";
	}

	auto explan = propagator->getExplanation(l);
	MAssert(explan!=nullPtrClause);

	if (verbosity() > 2) {
		printClause(explan);
	}
	return explan;
}

lbool PCSolver::getModelValue(Var v) {
	return getSolver().modelValue(mkPosLit(v));
}

litlist PCSolver::getEntailedLiterals() const {
	litlist list;
	auto firstdecision = getDecisions()[0];
	for (auto i = getTrail().cbegin(); i < getTrail().cend(); ++i) {
		if (*i == firstdecision) {
			break;
		}
		list.push_back(*i);
	}
	return list;
}

/* complexity O(#propagations on level)
 * @pre: p has been assigned in the current decision level!
 * Returns true if l was asserted before p
 */
bool PCSolver::assertedBefore(const Var& l, const Var& p) const {
	MAssert(value(mkPosLit(l))!=l_Undef && value(mkPosLit(p))!=l_Undef);

	if (getLevel(l) < getLevel(p)) {
		return true;
	}
	if (getTime(l) < getTime(p)) {
		return true;
	}

	return false;
}

int PCSolver::getTime(const Var& var) const {
	return trail->getTime(mkPosLit(var));
}

template<class T>
bool compareByPriority(const T& left, const T& right) {
	return left.priority < right.priority;
}

void PCSolver::finishParsing() {
	parsingfinished = true;
	sort(optimization.begin(), optimization.end(), compareByPriority<OptimStatement>);
	for (uint i = 1; i < optimization.size(); ++i) {
		if (optimization[i].priority == optimization[i - 1].priority) {
			throw idpexception("Two optimization statement cannot have the same priority.");
		}
	}

	propagations.resize(nVars(), NULL); //Lazy init

	auto val = getFactory().finishParsing();
	if (val== SATVAL::UNSAT) {
		notifyUnsat();
	}
}

rClause PCSolver::notifyFullAssignmentFound() {
	return getEventQueue().notifyFullAssignmentFound();
}

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolver::newDecisionLevel() {
	trail->notifyNewDecisionLevel();
	getEventQueue().notifyNewDecisionLevel();
}

void PCSolver::backtrackDecisionLevel(int untillevel, const Lit& decision) {
	if (monitoring) {
		monitor->notifyMonitor(untillevel);
	}

	trail->notifyBacktrack(untillevel);
	getEventQueue().notifyBacktrack(untillevel, decision);
}

void PCSolver::setAssumptions(const litlist& assumps) {
	getSATSolver()->setAssumptions(assumps);
}
lbool PCSolver::solve(bool search) {
	monitoring = monitor->hasMonitors();
	return getSATSolver()->solve(not search);
}

/**
 * Returns not-owning pointer
 *
 * During initialization, store the propagations to redo them later on.
 */
rClause PCSolver::propagate() {
	return getEventQueue().notifyPropagate();
}

SATVAL PCSolver::satState() const {
	return getSATSolver()->isUnsat() ? SATVAL::UNSAT : SATVAL::POS_SAT;
}

void PCSolver::notifyUnsat() {
	return getSATSolver()->notifyUnsat();
}

bool PCSolver::isDecided(Var var) {
	return getSATSolver()->isDecided(var);
}

void PCSolver::saveState() {
	saved = true;
	getEventQueue().saveState();
	getSolver().saveState();
}

void PCSolver::resetState() {
	if(saved){
		getSolver().resetState(); // First solver, with possible backtrack, afterwards reset propagators
								// So NEVER make the searchengine "EV_STATEFUL"!
		getEventQueue().resetState();
	}
	saved = false;
}

// PRINT METHODS

void PCSolver::printEnqueued(const Lit& p) const {
	clog << "> Enqueued " << toString(p) << "\n";
}

void PCSolver::printChoiceMade(int level, const Lit& l) const {
	if (modes().verbosity >= 2) {
		clog << "> Choice literal, dl " << level << ": " << toString(l) << ".\n";
	}
}

void PCSolver::printClause(rClause clause) const {
	getSolver().printClause(getClauseRef(clause));
}

void PCSolver::extractLitModel(std::shared_ptr<Model> fullmodel) {
	fullmodel->literalinterpretations.clear();
	for (uint64_t i = 0; i < nVars(); ++i) {
		if (value(mkPosLit(i)) == l_True) {
			fullmodel->literalinterpretations.push_back(mkLit(i, false));
		} else if (value(mkPosLit(i)) == l_False) {
			fullmodel->literalinterpretations.push_back(mkLit(i, true));
		}
	}
}

void PCSolver::extractVarModel(std::shared_ptr<Model> fullmodel) {
	fullmodel->variableassignments.clear();
	getFactory().includeCPModel(fullmodel->variableassignments);
#ifdef CPSUPPORT
	if(hasCPSolver()) {
		getCPSolver()->getVariableSubstitutions(fullmodel->variableassignments);
	}
#endif
}

std::shared_ptr<Model> PCSolver::getModel() {
	// Assert valid call!
	auto fullmodel = std::shared_ptr<Model>(new Model());
	extractLitModel(fullmodel);
	extractVarModel(fullmodel);
	return fullmodel;
}

void PCSolver::accept(ConstraintVisitor& visitor) {
	for (auto i = optimization.cbegin(); i < optimization.cend(); ++i) {
		switch ((*i).optim) {
		case Optim::AGG:
			visitor.visit(MinimizeAgg((*i).priority, (*i).agg_to_minimize->getSet()->getSetID(), (*i).agg_to_minimize->getType()));
			break;
		case Optim::LIST:
			visitor.visit(MinimizeOrderedList((*i).priority, (*i).to_minimize));
			break;
		case Optim::SUBSET:
			visitor.visit(MinimizeSubset((*i).priority, (*i).to_minimize));
			break;
		case Optim::VAR:
			visitor.visit(MinimizeVar((*i).priority, (*i).var->id()));
			break;
		}
	}
	// TODO any missing calls? (unfinished constraints in propagatorfactory, ...)
	getEventQueue().accept(visitor);
}

std::string PCSolver::toString(const Lit& lit) const {
	return printer->toString(lit);
}

int PCSolver::getNbOfFormulas() const {
	return getEventQueue().getNbOfFormulas() + optimization.size();
}
