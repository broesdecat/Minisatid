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
#include "InternalAdd.hpp"

#include "modules/aggsolver/AggSet.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

using Minisat::vec;

//Has to be value copy of modes!
PCSolverImpl::PCSolverImpl(SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer, bool oneshot) :
		_modes(modes),
		varcreator(varcreator),
		monitor(monitor),
		currentoptim(0),
		searchengine(NULL),
#ifdef CPSUPPORT
		cpsolver(NULL),
#endif
		factory(NULL),
		trail(new TimeTrail()),
		terminate(false),
		printer(printer),
		queue(NULL),
		monitoring(false){
	queue = new EventQueue(*this);
	searchengine = createSolver(this, oneshot);
#ifdef CPSUPPORT
	cpsolver = new CPSolver(this);
#endif

	factory = new PropagatorFactory(modes, this);

	if (verbosity() > 1) {
		modes.print(clog);
	}
}

PCSolverImpl::~PCSolverImpl() {
	delete (queue);
	// NOTE: solvers are deleted by the queue!
	delete (factory);
	delete (trail);
}


bool PCSolverImpl::hasCPSolver() const {
#ifdef CPSUPPORT
	return cpsolver!=NULL && cpsolver->isPresent();
#else
	return false;
#endif
}
SATVAL PCSolverImpl::findNextCPModel(){
#ifdef CPSUPPORT
	MAssert(hasCPSolver());
	if(not getCPSolver()->hasData()){
		return SATVAL::UNSAT;
	}
	return getCPSolver()->findNextModel()==nullPtrClause?SATVAL::POS_SAT:SATVAL::UNSAT;
#else
	throw idpexception("Calling methods on cpsolver while gecode is not compiled in.");
#endif
}

void PCSolverImpl::invalidate(litlist& clause) const {
	// Add negation of model as clause for next iteration.
	// By default: by adding all choice literals
	auto v = getSolver().getDecisions();
	for (auto i = v.cbegin(); i < v.cend(); ++i) {
		clause.push_back(~(*i));
	}
}
bool PCSolverImpl::moreModelsPossible() const{
	return getCurrentDecisionLevel() != getSolver().getNbOfAssumptions();
}

lbool PCSolverImpl::value(Lit p) const {
	return getSolver().value(p);
}
lbool PCSolverImpl::rootValue(Lit p) const {
	return getSolver().rootValue(p);
}
uint64_t PCSolverImpl::nVars() const {
	return getSolver().nbVars();
}
void PCSolverImpl::notifyTerminateRequested() {
	terminate = true;
}
bool PCSolverImpl::terminateRequested() const {
	return terminate;
}

const std::vector<Lit>& PCSolverImpl::getTrail() const {
	return trail->getTrail();
}

bool PCSolverImpl::isDecisionVar(Var var) {
	if ((uint64_t) var >= nVars()) {
		return false;
	}
	return getSATSolver()->isDecisionVar(var);
}
void PCSolverImpl::notifyDecisionVar(Var var) {
	getSATSolver()->setDecidable(var, true);
}

rClause PCSolverImpl::createClause(const Disjunction& clause, bool learned) {
	if (clause.literals.size() == 0) {
		return getSolver().makeClause({mkNegLit(dummy1), mkNegLit(dummy2)}, learned);
	} else if (clause.literals.size() == 1) {
		return getSolver().makeClause({clause.literals[0], mkNegLit(dummy1)}, learned);
	} else {
		return getSolver().makeClause(clause.literals, learned);
	}
}

void PCSolverImpl::acceptForDecidable(Var v, Propagator* prop) {
	getEventQueue().acceptForDecidable(v, prop);
}
void PCSolverImpl::notifyBecameDecidable(Var v) {
	getEventQueue().notifyBecameDecidable(v);
}

// NOTE: when adding a clause, this should be propagated asap
void PCSolverImpl::addLearnedClause(rClause c) {
	// FIXME method is incorrect if clause can propagate
	// FIXME method is incorrect if first two literals of clause are false, but possible others aren't
	getSolver().addLearnedClause(c);
}
int PCSolverImpl::getClauseSize(rClause cr) const {
	return getSolver().getClauseSize(cr);
}
Lit PCSolverImpl::getClauseLit(rClause cr, int i) const {
	return getSolver().getClauseLit(cr, i);
}

void PCSolverImpl::backtrackTo(int level) {
	getSolver().cancelUntil(level);
}

void PCSolverImpl::setTrue(const Lit& p, Propagator* module, rClause c) {
	MAssert(value(p)!=l_False && value(p)!=l_True);
	propagations[var(p)] = module;
	getSolver().uncheckedEnqueue(p, c);
}

void PCSolverImpl::notifySetTrue(const Lit& p) {
	getEventQueue().setTrue(p);
	trail->notifyPropagate(p);

	if (monitoring) {
		monitor->notifyMonitor(p, getCurrentDecisionLevel());
	}
}

int PCSolverImpl::getCurrentDecisionLevel() const {
	return getSolver().decisionLevel();
}

int PCSolverImpl::getLevel(int var) const {
	return getSolver().getLevel(var);
}

vector<Lit> PCSolverImpl::getDecisions() const {
	return getSolver().getDecisions();
}

bool PCSolverImpl::isAlreadyUsedInAnalyze(const Lit& lit) const {
	return getSolver().isAlreadyUsedInAnalyze(lit);
}

void PCSolverImpl::varBumpActivity(Var v) {
	getSolver().varBumpActivity(v);
}

void PCSolverImpl::varReduceActivity(Var v) {
	getSolver().varReduceActivity(v);
}

void PCSolverImpl::accept(Propagator* propagator) {
	getEventQueue().accept(propagator);
}

void PCSolverImpl::accept(GenWatch* const watch) {
	getEventQueue().accept(watch);
}

void PCSolverImpl::acceptForBacktrack(Propagator* propagator) {
	getEventQueue().acceptForBacktrack(propagator);
}
void PCSolverImpl::acceptForPropagation(Propagator* propagator) {
	getEventQueue().acceptForPropagation(propagator);
}

void PCSolverImpl::accept(Propagator* propagator, EVENT event) {
	getEventQueue().accept(propagator, event);
}

void PCSolverImpl::acceptBounds(IntView* var, Propagator* propagator) {
	getEventQueue().acceptBounds(var, propagator);
}

void PCSolverImpl::accept(Propagator* propagator, const Lit& lit, PRIORITY priority) {
	getEventQueue().accept(propagator, lit, priority);
}

Var PCSolverImpl::newVar() {
	auto newnbvars = nVars() + 1;
	auto var = varcreator->createVar();
	MAssert((uint64_t)var==newnbvars-1);
	getEventQueue().notifyNbOfVars(newnbvars); // IMPORTANT to do it before effectively creating it in the solver (might trigger grounding)
	createVar(var);
	MAssert(nVars()==newnbvars);
	return var;
}

/**
 * VARHEUR::DECIDE has precedence over NON_DECIDE for repeated calls to the same var!
 */
void PCSolverImpl::createVar(Var v) {
	MAssert(v>-1);

	if(((uint64_t)v)>=nVars()){
		getEventQueue().notifyNbOfVars(v+1); // IMPORTANT to do it before effectively creating vars in the solver (might trigger grounding)
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

int PCSolverImpl::newSetID() {
	return getFactory().newSetID();
}

void PCSolverImpl::notifyBoundsChanged(IntVar* var) {
	getEventQueue().notifyBoundsChanged(var);
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolverImpl::getExplanation(const Lit& l) {
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

lbool PCSolverImpl::getModelValue(Var v){
	return getSolver().modelValue(mkPosLit(v));
}

litlist PCSolverImpl::getEntailedLiterals() const{
	litlist list;
	auto firstdecision = getDecisions()[0];
	for(auto i=getTrail().cbegin(); i<getTrail().cend(); ++i) {
		if(*i==firstdecision){
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
bool PCSolverImpl::assertedBefore(const Var& l, const Var& p) const {
	MAssert(value(mkPosLit(l))!=l_Undef && value(mkPosLit(p))!=l_Undef);

	if (getLevel(l) < getLevel(p)) {
		return true;
	}
	if (getTime(l) < getTime(p)) {
		return true;
	}

	return false;
}

int PCSolverImpl::getTime(const Var& var) const {
	return trail->getTime(mkPosLit(var));
}

template<class T>
bool compareByPriority(const T& left, const T& right) {
	return left.priority < right.priority;
}

void PCSolverImpl::finishParsing() {
	sort(optimization.begin(), optimization.end(), compareByPriority<OptimStatement>);
	for (uint i = 1; i < optimization.size(); ++i) {
		if (optimization[i].priority == optimization[i - 1].priority) {
			throw idpexception("Two optimization statement cannot have the same priority.");
		}
	}

	dummy1 = newVar();
	Disjunction d1;
	d1.literals.push_back(mkLit(dummy1, false));
	add(d1, *this);
	dummy2 = newVar();
	Disjunction d2;
	d2.literals.push_back(mkLit(dummy2, false));
	add(d2, *this);

	propagations.resize(nVars(), NULL); //Lazy init

	if (getFactory().finishParsing() == SATVAL::UNSAT) {
		notifyUnsat();
	}
}

rClause PCSolverImpl::notifyFullAssignmentFound() {
	return getEventQueue().notifyFullAssignmentFound();
}

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolverImpl::newDecisionLevel() {
	trail->notifyNewDecisionLevel();
	getEventQueue().notifyNewDecisionLevel();
}

void PCSolverImpl::backtrackDecisionLevel(int untillevel, const Lit& decision) {
	if (monitoring) {
		monitor->notifyMonitor(untillevel);
	}

	trail->notifyBacktrack(untillevel);
	getEventQueue().notifyBacktrack(untillevel, decision);
}

void PCSolverImpl::setAssumptions(const litlist& assumps){
	getSATSolver()->setAssumptions(assumps);
}
lbool PCSolverImpl::solve(bool search) {
	monitoring = monitor->hasMonitors();
	return getSATSolver()->solve(not search);
}

/**
 * Returns not-owning pointer
 *
 * During initialization, store the propagations to redo them later on.
 */
rClause PCSolverImpl::propagate() {
	return getEventQueue().notifyPropagate();
}

SATVAL PCSolverImpl::satState() const {
	return getSATSolver()->isUnsat() ? SATVAL::UNSAT : SATVAL::POS_SAT;
}

void PCSolverImpl::notifyUnsat() {
	return getSATSolver()->notifyUnsat();
}

bool PCSolverImpl::isDecided(Var var) {
	return getSATSolver()->isDecided(var);
}

void PCSolverImpl::saveState() {
	getEventQueue().saveState();
	getSolver().saveState();
}

void PCSolverImpl::resetState() {
	getSolver().resetState(); // First solver, with possible backtrack, afterwards reset propagators
	getEventQueue().resetState();
}

// PRINT METHODS

void PCSolverImpl::printEnqueued(const Lit& p) const {
	clog << "> Enqueued " << toString(p) << "\n";
}

void PCSolverImpl::printChoiceMade(int level, const Lit& l) const {
	if (modes().verbosity >= 2) {
		clog << "> Choice literal, dl " << level << ": " << toString(l) << ".\n";
	}
}

void PCSolverImpl::printClause(rClause clause) const {
	getSolver().printClause(getClauseRef(clause));
}

void PCSolverImpl::extractLitModel(std::shared_ptr<Model> fullmodel) {
	fullmodel->literalinterpretations.clear();
	for (uint64_t i = 0; i < nVars(); ++i) {
		if (value(mkPosLit(i)) == l_True) {
			fullmodel->literalinterpretations.push_back(mkLit(i, false));
		} else if (value(mkPosLit(i)) == l_False) {
			fullmodel->literalinterpretations.push_back(mkLit(i, true));
		}
	}
}

void PCSolverImpl::extractVarModel(std::shared_ptr<Model> fullmodel) {
	fullmodel->variableassignments.clear();
	getFactory().includeCPModel(fullmodel->variableassignments);
#ifdef CPSUPPORT
	if(hasCPSolver()) {
		getCPSolver()->getVariableSubstitutions(fullmodel->variableassignments);
	}
#endif
}

std::shared_ptr<Model> PCSolverImpl::getModel() {
	// Assert valid call!
	auto fullmodel = std::shared_ptr<Model>(new Model());
	extractLitModel(fullmodel);
	extractVarModel(fullmodel);
	return fullmodel;
}

void PCSolverImpl::accept(ConstraintVisitor& visitor) {
	// TODO other necessary calls? (toString optimization, toString unfinished constraints, ...?
	getEventQueue().accept(visitor);
}

std::string PCSolverImpl::toString(const Lit& lit) const {
	return printer->toString(lit);
}

// @pre: decision level = 0
// FIXME add CNF printing too!
/*void PCSolverImpl::printTheory(ostream& stream){
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
