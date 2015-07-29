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
#include "satsolver/heuristics/Heuristics.hpp"
#include "modules/IntVar.hpp"

#include "theorysolvers/PropagatorFactory.hpp"
#include "theorysolvers/EventQueue.hpp"
#include "theorysolvers/TimeTrail.hpp"
#include "external/Space.hpp"
#include "datastructures/InternalAdd.hpp"

#include "modules/aggsolver/AggSet.hpp"
#include "external/ConstraintVisitor.hpp"

#include "TheorySimplifier.hpp"

#include "utils/NumericLimits.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

using Minisat::vec;

//Has to be value copy of modes!
PCSolver::PCSolver(TheoryID theoryID, SolverOption modes, Monitor* monitor, VarCreation* varcreator, LiteralPrinter* printer, bool oneshot)
		: theoryID(theoryID), _modes(modes), varcreator(varcreator), _outputvarsset(false), monitor(monitor),
		  parsingfinished(false), needNewFinishCall(false),
		  optimproblem(false), currentoptim(0),
		  searchengine(NULL),
#ifdef CPSUPPORT
			cpsolver(NULL),
#endif
			factory(NULL),
			trail(new TimeTrail()), minnewset(-1), terminate(false), printer(printer), queue(NULL),
			groundingCalls(0), maxCallsBeforeRestart(100) {
	queue = new EventQueue(*this);
	searchengine = createSolver(this, oneshot);

	auto propfactory = new PropagatorFactory(modes, this);
	if(modes.usesimplifier && not modes.lazy){
		factory = new TheorySimplifier(propfactory);
	}else{
		factory = propfactory;
	}

	if (verbosity() > 5) {
		modes.print(clog);
	}

	dummy1 = newAtom();
	dummy2 = newAtom();
	Disjunction disj({ mkPosLit(dummy1) });
	disj.theoryid = getTheoryID();
	Disjunction disj2({ mkPosLit(dummy2) });
	disj2.theoryid = getTheoryID();
	internalAdd(disj, getTheoryID(), *this);
	internalAdd(disj2, getTheoryID(), *this);
}

Lit PCSolver::getTrueLit() const {
	return mkPosLit(dummy1);
}
Lit PCSolver::getFalseLit() const {
	return mkNegLit(dummy1);
}

PCSolver::~PCSolver() {
	delete (queue);
	// NOTE: solvers are deleted by the queue!
	delete (factory);
	delete (trail);
}

void PCSolver::invalidate(litlist& clause) const {
	if(_outputvarsset){
		for(auto var: _outputvars){
			if(value(mkPosLit(var))==l_Undef){
				continue;
			}
			clause.push_back(value(mkPosLit(var))==l_True?mkNegLit(var):mkPosLit(var));
		}
	}else{
		// Add negation of model as clause for next iteration.
		// By default: by adding all choice literals
		auto v = getSolver().getDecisions();
		for (auto i = v.cbegin(); i < v.cend(); ++i) {
			clause.push_back(~(*i));
		}
	}
}
bool PCSolver::moreModelsPossible() const {
	return getCurrentDecisionLevel() != getSolver().getNbOfAssumptions();
}

bool PCSolver::isTwoValued() const{
	return getSolver().isTwoValued();
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

void PCSolver::addOutputVars(const std::vector<Atom>& outputvars){
	_outputvarsset = true;
	for(auto var: outputvars){
		_outputvars.insert(var);
	}
}

bool PCSolver::isDecisionVar(Atom var) {
	if ((uint64_t) var >= nVars()) {
		return false;
	}
	return getSATSolver()->isDecisionVar(var);
}
void PCSolver::notifyDecisionVar(Atom var) {
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

void PCSolver::acceptForDecidable(Atom v, Propagator* prop) {
	getEventQueue().acceptForDecidable(v, prop);
}
void PCSolver::notifyBecameDecidable(Atom v) {
	if (verbosity() > 5) {
		clog << ">>> Making " << toString(mkPosLit(v)) << " decidable.\n";
	}
	getEventQueue().notifyBecameDecidable(v);
}

void PCSolver::addLearnedClause(rClause c) {
	getSolver().addLearnedClause(c);
}
void PCSolver::addConflictClause(rClause c) {
	getSolver().addConflictClause(c);
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

	if (hasMonitors()) {
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

void PCSolver::accept(Propagator* propagator) {
	getEventQueue().accept(propagator);
}

void PCSolver::accept(GenWatch* const watch) {
	getEventQueue().accept(watch);
}

void PCSolver::acceptForPropagation(Propagator* propagator, PRIORITY priority) {
	getEventQueue().acceptForPropagation(propagator, priority);
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

VarID PCSolver::newID(){
	return varcreator->createID();
}
IntView* PCSolver::getIntView(VarID id, Weight bound){
	return getFactory().getIntView(id, bound);
}
Atom PCSolver::newAtom() {
	auto var = varcreator->createVar();
	if ((uint64_t) var >= nVars()) {
		getEventQueue().notifyNbOfVars(var); // IMPORTANT to do it before effectively creating it in the solver (might trigger grounding)
	}
	createVar(var, getTheoryID());
	return var;
}

/**
 * VARHEUR::DECIDE has precedence over NON_DECIDE for repeated calls to the same var!
 */
void PCSolver::createVar(Atom v, TheoryID ) {
	//MAssert(getTheoryID()==theoryID); Place back if theoryId is needed
	MAssert(v>-1);

	if (((uint64_t) v) >= nVars()) {
		getEventQueue().notifyNbOfVars(v + 1); // IMPORTANT to do it before effectively creating vars in the solver (might trigger grounding)
		while (((uint64_t) v) >= nVars()) {
			getSolver().newVar(modes().polarity == Polarity::TRUE ? l_False: modes().polarity == Polarity::FALSE ? l_True : l_Undef, false);
		}
	}

	if (not getSolver().isDecisionVar(v)) {
		// If lazy, do not decide for literals in decisions
		// NOTE: only use this if the watches mechanism of the constraint will take care of making literal decidable if necessary
		auto decide = modes().watchedrelevance ? VARHEUR::DONT_DECIDE : VARHEUR::DECIDE;
		getSolver().setDecidable(v, decide == VARHEUR::DECIDE);
	}
	if (propagations.size() < nVars()) { //Lazy init
		propagations.resize(nVars(), NULL);
	}
}

void PCSolver::notifyHeuristicOfLazyAtom(Atom v, Atom v1, Atom v2){
	getHeuristic().notifyOfLazyAtom(v, v1, v2);
}

MinisatHeuristic& PCSolver::getHeuristic(){
	return getSATSolver()->getHeuristic();
}

void PCSolver::notifyBoundsChanged(IntVar* var) {
	getEventQueue().notifyBoundsChanged(var);
}

/**
 * Returns OWNING pointer (faster).
 * TODO this could should NOT be used to externally get an explanation.
 * 		It might malfunction as it is not stored if the SAT-solver was the last one to propagate a literal.
 */
rClause PCSolver::getExplanation(const Lit& l) {
	MAssert(value(l)!=l_Undef);
	if (modes().verbosity > 6) {
		clog << "Generating explanation for " << toString(l) << "\n";
	}

	auto propagator = propagations[var(l)];
	auto explan = nullPtrClause;
	if (propagator == NULL) {
		//If this happens, there is usually an error in the generated explanations, was only requested by the now removed symmetry propagator.
		if (modes().verbosity > 6) {
			clog << "\tGenerated by SAT-solver: ";
		}
		explan = getSolver().reason(var(l));
	} else {
		if (modes().verbosity > 6) {
			clog << "\tGenerated by " << propagator->getName() << ": ";
		}
		explan = propagator->getExplanation(l);
	}
	//MAssert(explan!=nullPtrClause); TODO NOTE it is now allowed to request non-existing explanations!
	if (verbosity() > 6) {
		if (explan != nullPtrClause) {
			printClause(explan);
		} else {
			clog << "root or decided\n";
		}
	}
	return explan;
}

lbool PCSolver::getModelValue(Atom v) {
	return getSolver().modelValue(mkPosLit(v));
}
lbool PCSolver::getModelValue(const Lit & lit) {
	return getSolver().modelValue(lit);
}
MXStatistics PCSolver::getStats() const{
	return MXStatistics{getSolver().getNbOfRestarts(),getSolver().getNbOfDecision(),getSolver().getNbOfPropagations(),getSolver().getNbOfConflicts(), getSolver().getTimeOfFirstDecision()};
}

litlist PCSolver::getEntailedLiterals() const {
	litlist list;
	auto firstdecision = getDecisions().size()>0?getDecisions()[0]:mkLit(getMaxElem<int>());
	for (auto i = getTrail().cbegin(); i < getTrail().cend(); ++i) {
		if (*i == firstdecision) {
			break;
		}
		list.push_back(*i);
	}
	return list;
}

/* complexity O(#propagations on level)
 * Returns true if l was asserted before p
 */
bool PCSolver::assertedBefore(const Atom& l, const Atom& p) const {
	MAssert(value(mkPosLit(l))!=l_Undef || value(mkPosLit(p))!=l_Undef);
	if (value(mkPosLit(l)) == l_Undef) {
		return false;
	}
	if (value(mkPosLit(p)) == l_Undef) {
		return true;
	}

	if (getLevel(l) < getLevel(p)) {
		return true;
	}
	if (getTime(l) < getTime(p)) {
		return true;
	}

	return false;
}

int PCSolver::getTime(const Atom& var) const {
	return trail->getTime(mkPosLit(var));
}

template<class T>
bool compareByPriority(const T& left, const T& right) {
	return left.priority < right.priority;
}

void PCSolver::notifyFinishParsingNeed(){
	if(isUnsat()){
		return;
	}
	needNewFinishCall = true;
	if(parsingfinished){
		finishParsing();
	}
}

void PCSolver::finishParsing() {
	sort(optimization.begin(), optimization.end(), compareByPriority<OptimStatement>);
	for (uint i = 1; i < optimization.size(); ++i) {
		if (optimization[i].priority == optimization[i - 1].priority) {
			throw idpexception("Two optimization statement cannot have the same priority.");
		}
	}

	while(true){
		needNewFinishCall = false;
		auto val = getFactory().finish();
		if (val == SATVAL::UNSAT) {
			notifyUnsat();
			needNewFinishCall = false;
		}
		if(not needNewFinishCall){
			break;
		}
	}
	needNewFinishCall = false;
	parsingfinished = true;
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
	if (hasMonitors()) {
		monitor->notifyMonitor(untillevel);
	}

	trail->notifyBacktrack(untillevel);
	getEventQueue().notifyBacktrack(untillevel, decision);
}

bool PCSolver::hasMonitors() const{
	return monitor!=NULL && monitor->hasMonitors();
}

void PCSolver::addAssumption(const Lit assump){
  getSATSolver()->addAssumption(assump);
}
void PCSolver::removeAssumption(const Lit assump){
  getSATSolver()->removeAssumption(assump);
}
void PCSolver::clearAssumptions(){
  getSATSolver()->clearAssumptions();
}
lbool PCSolver::solve(bool search) {
	return getSATSolver()->solve(not search);
}
litlist PCSolver::getUnsatExplanation() const {
	MAssert(isUnsat());
	return getSATSolver()->getUnsatExplanation();
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

bool PCSolver::isDecided(Atom var) {
	return getSATSolver()->isDecided(var);
}

void PCSolver::getOutOfUnsat(){
  getSolver().getOutOfUnsat();
}

// PRINT METHODS

void PCSolver::printEnqueued(const Lit& p) const {
	clog << "> Enqueued " << toString(p) << "\n";
}

void PCSolver::printChoiceMade(int level, const Lit& l) const {
	if (modes().verbosity >= 1) {
		clog << "> Choice literal, dl " << level << ": " << toString(l) << ".\n";
	}
}

void PCSolver::printClause(rClause clause) const {
	MAssert(clause!=nullPtrClause);
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
			visitor.add(MinimizeAgg((*i).priority, (*i).agg_to_minimize->getSet()->getSetID(), (*i).agg_to_minimize->getType()));
			break;
		case Optim::SUBSET:
			visitor.add(MinimizeSubset((*i).priority, (*i).to_minimize));
			break;
		case Optim::VAR:
			visitor.add(OptimizeVar((*i).priority, (*i).var->getID(), (*i).minimize));
			break;
		}
	}
	// TODO any missing calls? (unfinished constraints in propagatorfactory, ...)
	getEventQueue().accept(visitor);
}

void PCSolver::setString(const Atom& lit, const std::string& name){
	printer->setString(lit, name);
}

bool PCSolver::isTseitin(const Atom& atom) const {
	return printer->isTseitin(atom);
}
std::string PCSolver::toString(VarID id) const {
	return printer->toString(id);
}
std::string PCSolver::toString(const Lit& lit) const {
	return printer->toString(lit);
}

int PCSolver::getNbOfFormulas() const {
	return getEventQueue().getNbOfFormulas() + optimization.size();
}

Lit PCSolver::getLit(VarID var, EqType eq, Weight bound){
	MAssert(eq==EqType::EQ || eq==EqType::LEQ);
	auto lit = getFactory().exists(CPBinaryRel(mkPosLit(0), var, eq, bound));
	if(lit.x==0){
		auto atom = newAtom();
		getHeuristic().setPolarity(atom, getSATSolver()->getRandNumber()<0.5); // FIXME not included in random seed!
		stringstream ss;
		if(eq==EqType::LEQ){
			ss<< toString(var) << "=<" << bound;
		}else{
			ss<< toString(var) << "=" << bound;
		}
		setString(atom,ss.str());

		auto outLit = mkPosLit(atom);
		if(_outputvarids.count(var)>0){
			vector<Atom> output = {atom};
			this->addOutputVars(output);
		}
		return outLit;
	}else{
		return lit;
	}
}

void PCSolver::notifyGroundingCall(){
	if(getCurrentDecisionLevel()==0 || not modes().userandomizedrestarts){
		return;
	}
	groundingCalls++;
	if(groundingCalls>maxCallsBeforeRestart){
		maxCallsBeforeRestart *= 1.3;
		getSolver().randomizedRestart();
	}
}

void PCSolver::addOutputVarId(const VarID &vid) {
	_outputvarids.insert(vid);
}

bool PCSolver::isOutputVarId(const VarID &vid) {
	return _outputvarids.count(vid)>0;
}
