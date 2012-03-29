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
#include "modules/CPSolver.hpp"
#include "modules/IntVar.hpp"
#include "wrapper/InterfaceImpl.hpp"

#include "theorysolvers/PropagatorFactory.hpp"
#include "theorysolvers/EventQueue.hpp"
#include "theorysolvers/TimeTrail.hpp"

#include "modules/aggsolver/AggSet.hpp"
#include "external/DataAndInference.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

using Minisat::vec;

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes) :
		_modes(modes), searchengine(NULL),
#ifdef CPSUPPORT //TODO create dummy implemententation of CPSolver to remove all the ifdefs
				cpsolver(NULL),
#endif
		queue(NULL),
		factory(NULL),
		state(THEORY_PARSING),
		trail(new TimeTrail()),
		state_savedlevel(0), state_savingclauses(false),
		terminate(false){

	queue = new EventQueue(*this);

	searchengine = createSolver(this);
#ifdef CPSUPPORT
	cpsolver = new CPSolver(this);
#endif

	factory = new PropagatorFactory(modes, this);

	if(verbosity()>1){
		modes.print(clog);
	}
}

PCSolver::~PCSolver() {
	delete (queue);
	delete (searchengine);
#ifdef CPSUPPORT
	delete(cpsolver);
#endif
	delete(factory);
	delete(trail);
}

#ifdef CPSUPPORT
bool PCSolver::hasCPSolver() const {
	return cpsolver!=NULL && cpsolver->isPresent();
}
#endif

lbool PCSolver::value(Var x) const {
	return getSolver().value(x);
}
lbool PCSolver::value(Lit p) const {
	return getSolver().value(p);
}
uint64_t PCSolver::nVars() const {
	return getSolver().nbVars();
}
void PCSolver::notifyTerminateRequested(){
	terminate = true;
}
bool PCSolver::terminateRequested() const{
	return terminate;
}

const std::vector<Lit>& PCSolver::getTrail() const { return trail->getTrail(); }

bool PCSolver::isDecisionVar(Var var) {
	if((uint64_t)var>=nVars()){
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

rClause PCSolver::createClause(const InnerDisjunction& clause, bool learned) {
	if (clause.literals.size() == 0) {
		vec<Lit> dummylits; //INVAR, solver does not simplify learned clauses
		dummylits.push(mkLit(dummy1, true));
		dummylits.push(mkLit(dummy2, true));
		return getSolver().makeClause(dummylits, learned);
	} else if (clause.literals.size() == 1) {
		vec<Lit> dummylits;
		dummylits.push(clause.literals[0]);
		dummylits.push(mkLit(dummy1, true));
		return getSolver().makeClause(dummylits, learned);
	} else {
		vec<Lit> lits;
		for(auto lit = clause.literals.cbegin(); lit!=clause.literals.cend(); ++lit){
			lits.push(*lit);
		}
		return getSolver().makeClause(lits, learned);
	}
}

// NOTE: when adding a clause, this should be propagated asap
void PCSolver::addLearnedClause(rClause c) {
	// FIXME method is incorrect if clause can propagate
	// FIXME method is incorrect if first two literals of clause are false, but possible others aren't
	getSolver().addLearnedClause(c);
//FIXME	getEventQueue().acceptForPropagation(getSATSolver());
}
void PCSolver::removeClause(rClause c) {
	getSolver().removeClause(c);
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
	assert(value(p)!=l_False && value(p)!=l_True);
	propagations[var(p)] = module;
	getSolver().uncheckedEnqueue(p, c);
}

void PCSolver::notifySetTrue(const Lit& p) {
	getEventQueue().setTrue(p);
	trail->notifyPropagate(p);

	if (monitor!=NULL) {
		monitor->notifyMonitor(p, getCurrentDecisionLevel());
	}
}

int PCSolver::getCurrentDecisionLevel() const {
	return getSolver().decisionLevel();
}

bool PCSolver::handleConflict(rClause conflict){
	return getSolver().handleConflict(conflict);
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

bool PCSolver::hasTotalModel() {
	return getSolver().totalModelFound();
}

void PCSolver::varBumpActivity(Var v) {
	getSolver().varBumpActivity(v);
}

void PCSolver::varReduceActivity(Var v){
	getSolver().varReduceActivity(v);
}

void PCSolver::accept(Propagator* propagator) {
	getEventQueue().accept(propagator);
}

void PCSolver::accept(GenWatch* const watch){
	getEventQueue().accept(watch);
}

void PCSolver::acceptForBacktrack(Propagator* propagator){
	getEventQueue().acceptForBacktrack(propagator);
}
void PCSolver::acceptForPropagation(Propagator* propagator){
	getEventQueue().acceptForPropagation(propagator);
}

void PCSolver::accept(Propagator* propagator, EVENT event){
	getEventQueue().accept(propagator, event);
}

void PCSolver::acceptBounds(IntView* var, Propagator* propagator){
	getEventQueue().acceptBounds(var, propagator);
}

void PCSolver::accept(Propagator* propagator, const Lit& lit, PRIORITY priority){
	getEventQueue().accept(propagator, lit, priority);
}

void PCSolver::acceptFinishParsing(Propagator* propagator, bool late){
	getEventQueue().acceptFinishParsing(propagator, late);
}

void PCSolver::acceptForDecidable(Var v, Propagator* prop){
	getEventQueue().acceptForDecidable(v, prop);
}
void PCSolver::notifyBecameDecidable(Var v){
	MAssert((uint64_t)v<nVars());
	getEventQueue().notifyBecameDecidable(v);
}

void PCSolver::preventPropagation(){
	getEventQueue().preventPropagation();
}
void PCSolver::allowPropagation(){
	getEventQueue().allowPropagation();
}

Var PCSolver::newVar() {
	auto v = varcreator->createVar();
	add(v);
	return v;
}

int	PCSolver::newSetID(){
	// FIXME assert(!isParsing());
	return getFactory().newSetID();
}

rClause PCSolver::checkFullAssignment() {
	assert(satState()!=SATVAL::UNSAT);
	return getEventQueue().notifyFullAssignmentFound();
}

void PCSolver::notifyBoundsChanged(IntVar* var){
	getEventQueue().notifyBoundsChanged(var);
}

void PCSolver::notifyClauseAdded(rClause clauseID){
	getEventQueue().notifyClauseAdded(clauseID);
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(const Lit& l) {
	if (modes().verbosity > 2) {
		clog << "Generating explanation for " << l << ", ";
	}

	Propagator* propagator = propagations[var(l)];
	assert(propagator!=NULL);
	//If this happens, there is usually an error in the generated explanations!

	if (modes().verbosity > 2) {
		clog << "Generated by " << propagator->getName() << ": ";
	}

	rClause explan = propagator->getExplanation(l);
	assert(explan!=nullPtrClause);

	if (verbosity() > 2) {
		print(explan, *this);
		clog << "\n";
	}
	return explan;
}

/* complexity O(#propagations on level)
 * @pre: p has been assigned in the current decision level!
 * Returns true if l was asserted before p
 */
bool PCSolver::assertedBefore(const Var& l, const Var& p) const {
	assert(value(l)!=l_Undef && value(p)!=l_Undef);

	if(getLevel(l) < getLevel(p)) {
		return true;
	}
	if(getTime(l)<getTime(p)){
		return true;
	}

	return false;
}

/**
 * VARHEUR::DECIDE has precedence over NON_DECIDE for repeated calls to the same var!
 */
void PCSolver::createVar(Var v, VARHEUR decide) {
	assert(v>-1);

	while (((uint64_t) v) >= nVars()) {
		getSolver().newVar(modes().polarity == Polarity::TRUE ? l_True : modes().polarity == Polarity::FALSE ? l_False : l_Undef, false);
	}

	if(not getSolver().isDecisionVar(v)){
		getSolver().setDecidable(v, decide==VARHEUR::DECIDE);
		if (/* FIXME isInitialized() &&*/ propagations.size()<nVars()) { //Lazy init
			propagations.resize(nVars(), NULL);
		}
	}
}

void PCSolver::notifyVarAdded(){
	getEventQueue().notifyVarAdded();
}

int	PCSolver::getTime(const Var& var) const{
	return trail->getTime(mkPosLit(var));
}

void PCSolver::finishParsing() {
	if(state!=THEORY_INITIALIZED){
		state = THEORY_INITIALIZING;
		dummy1 = newVar();
		InnerDisjunction d1;
		d1.literals.push_back(mkLit(dummy1, false));
		add(d1);
		dummy2 = newVar();
		InnerDisjunction d2;
		d2.literals.push_back(mkLit(dummy2, false));
		add(d2);

		propagations.resize(nVars(), NULL); //Lazy init
		state = THEORY_INITIALIZED;
		if(getFactory().finishParsing()==SATVAL::UNSAT){
			notifyUnsat();
		}
	}

	if(isUnsat()){
		return;
	}

	getEventQueue().finishParsing();
	if (modes().useaggheur) {
		getSATSolver()->notifyCustomHeur();
	}
}

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolver::newDecisionLevel() {
	trail->notifyNewDecisionLevel();
	getEventQueue().notifyNewDecisionLevel();
}

void PCSolver::backtrackDecisionLevel(int untillevel, const Lit& decision) {
	if (monitor!=NULL) {
		monitor->notifyMonitor(untillevel);
	}

	trail->notifyBacktrack(untillevel);
	getEventQueue().notifyBacktrack(untillevel, decision);
}

lbool PCSolver::solve(const litlist& assumptions, bool search){
	return getSATSolver()->solve(assumptions, not search);
}

void PCSolver::addOptimization(Optim type, const litlist& literals){
	optimcreation->addOptimization(type, literals);
}
void PCSolver::addAggOptimization(Agg* aggmnmz){
	optimcreation->addAggOptimization(aggmnmz);
}

/**
 * Returns not-owning pointer
 *
 * During initialization, store the propagations to redo them later on.
 */
rClause PCSolver::propagate() {
	return getEventQueue().notifyPropagate();
}

int PCSolver::getNbOfFormulas() const {
	return getEventQueue().getNbOfFormulas();
}

SATVAL PCSolver::satState() const{
	return getSATSolver()->isUnsat()?SATVAL::UNSAT:SATVAL::POS_SAT;
}

void PCSolver::notifyUnsat() {
	return getSATSolver()->notifyUnsat();
}

bool PCSolver::isDecided(Var var){
	return getSATSolver()->isDecided(var);
}

Var PCSolver::changeBranchChoice(const Var& chosenvar) {
	return getEventQueue().notifyBranchChoice(chosenvar);
}

void PCSolver::saveState() {
	state_savedlevel = getCurrentDecisionLevel();
	state_savingclauses = true;
}

void PCSolver::resetState() {
	backtrackTo(state_savedlevel);
	assert(state_savedlevel == getCurrentDecisionLevel());
	state_savingclauses = false;

	throw idpexception("Resetting state is incorrect.\n"); // FIXME
	//getSolver().removeClauses(state_savedclauses);
	state_savedclauses.clear();
	//getSolver().removeAllLearnedClauses();
}

// PRINT METHODS

void PCSolver::printEnqueued(const Lit& p) const {
	clog << "> Enqueued " << p << "\n";
}

void PCSolver::printChoiceMade(int level, const Lit& l) const {
	if (modes().verbosity >= 2) {
		clog << "> Choice literal, dl " << level << ": " << l << ".\n";
	}
}

void PCSolver::printClause(rClause clause) const {
	getSolver().printClause(getClauseRef(clause));
}

void PCSolver::extractLitModel(std::shared_ptr<InnerModel> fullmodel) {
	fullmodel->litassignments.clear();
	// FIXME implement more efficiently in the satsolver?
	for (uint64_t i = 0; i < nVars(); ++i) {
		if (value(i) == l_True) {
			fullmodel->litassignments.push_back(mkLit(i, false));
		} else if (value(i) == l_False) {
			fullmodel->litassignments.push_back(mkLit(i, true));
		}
	}
}

void PCSolver::extractVarModel(std::shared_ptr<InnerModel> fullmodel) {
	fullmodel->varassignments.clear();
	getFactory().includeCPModel(fullmodel->varassignments);
#ifdef CPSUPPORT
	if(hasCPSolver()) {
		getCPSolver().getVariableSubstitutions(fullmodel->varassignments);
	}
#endif
}

std::shared_ptr<InnerModel> PCSolver::getModel(){
	// Assert valid call!
	auto fullmodel = std::shared_ptr<InnerModel>(new InnerModel());
	extractLitModel(fullmodel);
	extractVarModel(fullmodel);
	return fullmodel;
}

lbool PCSolver::getModelValue(Var v){
	return getSATSolver()->modelValue(v);
}

// @pre: decision level = 0
// TODO
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
