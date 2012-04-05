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

#include "modules/aggsolver/AggSet.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

using Minisat::vec;

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer) :
		_modes(modes), searchengine(NULL), monitor(monitor), varcreator(varcreator), printer(printer),
#ifdef CPSUPPORT
				cpsolver(NULL),
#endif
				queue(NULL), factory(NULL), trail(new TimeTrail()), terminate(false) {
	queue = new EventQueue(*this);
	searchengine = createSolver(this);
#ifdef CPSUPPORT
	cpsolver = new CPSolver(this);
#endif

	factory = new PropagatorFactory(modes, this);

	if (verbosity() > 1) {
		modes.print(clog);
	}
}

PCSolver::~PCSolver() {
	delete (queue);
	delete (searchengine);
#ifdef CPSUPPORT
	delete(cpsolver);
#endif
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
SATVAL PCSolver::findNextCPModel(){
#ifdef CPSUPPORT
	MAssert(hasCPSolver());
	if(not getCPSolver().hasData()){
		return SATVAL::UNSAT;
	}
	return getCPSolver().findNextModel()==nullPtrClause?SATVAL::POS_SAT:SATVAL::UNSAT;
#else
	throw idpexception("Calling methods on cpsolver while gecode is not compiled in.");
#endif
}


VARHEUR PCSolver::lazyDecide() const {
	return modes().lazy ? VARHEUR::DONT_DECIDE : VARHEUR::DECIDE;
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
void PCSolver::notifyNonDecisionVar(Var var) {
	getSATSolver()->setDecidable(var, false);
}
void PCSolver::notifyDecisionVar(Var var) {
	getSATSolver()->setDecidable(var, true);
}

rClause PCSolver::createClause(const Disjunction& clause, bool learned) {
	if (clause.literals.size() == 0) {
		return getSolver().makeClause({mkNegLit(dummy1), mkNegLit(dummy2)}, learned);
	} else if (clause.literals.size() == 1) {
		return getSolver().makeClause({clause.literals[0], mkNegLit(dummy1)}, learned);
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

// NOTE: when adding a clause, this should be propagated asap
void PCSolver::addLearnedClause(rClause c) {
	// FIXME method is incorrect if clause can propagate
	// FIXME method is incorrect if first two literals of clause are false, but possible others aren't
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
	MAssert(value(p)!=l_False && value(p)!=l_True);
	propagations[var(p)] = module;
	getSolver().uncheckedEnqueue(p, c);
}

void PCSolver::notifySetTrue(const Lit& p) {
	getEventQueue().setTrue(p);
	trail->notifyPropagate(p);

	if (monitor != NULL) {
		monitor->notifyMonitor(p, getCurrentDecisionLevel());
	}
}

int PCSolver::getCurrentDecisionLevel() const {
	return getSolver().decisionLevel();
}

int PCSolver::getLevel(int var) const {
	return getSolver().getLevel(var);
}

int PCSolver::getStartLastLevel() const {
	return getSolver().getStartLastLevel();
}

int PCSolver::getNbDecisions() const {
	return getSolver().decisionLevel();
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
	auto newnbvars = nVars() + 1;
	auto var = varcreator->createVar();
	MAssert(var==newnbvars-1);
	getEventQueue().notifyNbOfVars(newnbvars); // IMPORTANT to do it before effectively creating it in the solver (might trigger grounding)
	createVar(var, lazyDecide());
	MAssert(nVars()==newnbvars);
	return var;
}

void PCSolver::addVars(const std::vector<Var>& vars, VARHEUR heur) {
	for (auto i = vars.cbegin(); i < vars.cend(); ++i) {
		createVar(*i, heur);
	}
}

/**
 * VARHEUR::DECIDE has precedence over NON_DECIDE for repeated calls to the same var!
 */
void PCSolver::createVar(Var v, VARHEUR decide) {
	MAssert(v>-1);

	if(((uint64_t)v)>=nVars()){
		getEventQueue().notifyNbOfVars(v+1); // IMPORTANT to do it before effectively creating vars in the solver (might trigger grounding)
		while (((uint64_t) v) >= nVars()) {
			getSolver().newVar(modes().polarity == Polarity::TRUE ? l_True : modes().polarity == Polarity::FALSE ? l_False : l_Undef, false);
		}
	}

	if (not getSolver().isDecisionVar(v)) {
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
	MAssert(propagator!=NULL);
	//If this happens, there is usually an error in the generated explanations!

	if (modes().verbosity > 2) {
		clog << "Generated by " << propagator->getName() << ": ";
	}

	auto explan = propagator->getExplanation(l);
	// TODO add unsat core extraction here, but getExplan should not return an already created clause then.
	// add new class UnsatCoreManager to the PCSolver fields
	//	which associates at least one marker literal to each propagator
	//		each propagator then has to know the ids of its associated constraints!
	MAssert(explan!=nullPtrClause);

	if (verbosity() > 2) {
		printClause(explan);
	}
	return explan;
}

lbool PCSolver::getModelValue(Var v){
	return getSolver().modelValue(mkPosLit(v));
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
	sort(optimization.begin(), optimization.end(), compareByPriority<OptimStatement>);
	for (int i = 1; i < optimization.size(); ++i) {
		if (optimization[i].priority == optimization[i - 1].priority) {
			throw idpexception("Two optimization statement cannot have the same priority.");
		}
	}

	dummy1 = newVar();
	Disjunction d1;
	d1.literals.push_back(mkLit(dummy1, false));
	add(d1);
	dummy2 = newVar();
	Disjunction d2;
	d2.literals.push_back(mkLit(dummy2, false));
	add(d2);

	propagations.resize(nVars(), NULL); //Lazy init

	if (getFactory().finishParsing() == SATVAL::UNSAT) {
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
	if (monitor != NULL) {
		monitor->notifyMonitor(untillevel);
	}

	trail->notifyBacktrack(untillevel);
	getEventQueue().notifyBacktrack(untillevel, decision);
}

lbool PCSolver::solve(const litlist& assumptions, bool search) {
	return getSATSolver()->solve(assumptions, not search);
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
	// FIXME
//	state_savedlevel = getCurrentDecisionLevel();
//	state_savingclauses = true;
}

void PCSolver::resetState() {
	// FIXME
//	backtrackTo(state_savedlevel);
//	MAssert(state_savedlevel == getCurrentDecisionLevel());
//	state_savingclauses = false;

	throw notYetImplemented("Resetting state.\n");
	//getSolver().removeClauses(state_savedclauses);
//	state_savedclauses.clear();
	//getSolver().removeAllLearnedClauses();
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
		getCPSolver().getVariableSubstitutions(fullmodel->variableassignments);
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
	// TODO other necessary calls? (toString optimization, toString unfinished constraints, ...?
	getEventQueue().accept(visitor);
}

std::string PCSolver::toString(const Lit& lit) const {
	return printer->toString(lit);
}

// @pre: decision level = 0
// FIXME add CNF printing too!
/*void PCSolver::printTheory(ostream& stream){
 stringstream ss;
 std::set<Var> printedvars;
 int nbclauses = 0;
 nbclauses += getSATSolver()->printECNF(ss, printedvars);
 if(modes().tocnf){
 getEventQueue().printECNF(ss, printedvars);
 getParent().printTranslation(ss, printedvars);
 stream <<"p ecnf\n";
 }else{
 stream <<"p cnf " <<printedvars.size()+1 <<" " <<nbclauses <<"\n";
 }
 stream <<ss.str();
 clog <<"Currently not printing out any other constructs than clauses from the theory.";
 }*/
