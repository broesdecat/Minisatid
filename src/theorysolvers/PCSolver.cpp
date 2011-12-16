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
#include "modules/ModSolver.hpp"
#include "modules/CPSolver.hpp"
#include "modules/IntVar.hpp"
#include "wrapper/InterfaceImpl.hpp"

#include "theorysolvers/PropagatorFactory.hpp"
#include "theorysolvers/EventQueue.hpp"
#include "theorysolvers/TimeTrail.hpp"

#include "modules/aggsolver/AggSet.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

using Minisat::vec;

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes, MinisatID::WrapperPimpl& inter, int ID) :
		LogicSolver(modes, inter), ID(ID), searchengine(NULL),
#ifdef CPSUPPORT //TODO create dummy implemententation of CPSolver to remove all the ifdefs
				cpsolver(NULL),
#endif
		queue(NULL),
		factory(NULL),
		state(THEORY_PARSING),
		trail(new TimeTrail()),
		optim(Optim::NONE), head(-1),
		state_savedlevel(0), state_savingclauses(false){

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

bool PCSolver::isDecisionVar(Var var) {
	if(var>=nVars()){
		return false;
	}
	return getSATSolver()->isDecisionVar(var);
}
void PCSolver::notifyNonDecisionVar(Var var) {
	cerr <<"Make not decided variable " <<getPrintableVar(var) <<"\n";
	getSATSolver()->setDecisionVar(var, false);
}
void PCSolver::notifyDecisionVar(Var var) {
	cerr <<"Make decided variable " <<getPrintableVar(var) <<"\n";
	getSATSolver()->setDecisionVar(var, true);
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

	if (isBeingMonitored()) {
		InnerPropagation prop;
		prop.decisionlevel = getCurrentDecisionLevel();
		prop.propagation = p;
		notifyMonitor(prop);
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

bool PCSolver::hasTotalModel() {
	return getSolver().totalModelFound();
}

void PCSolver::varBumpActivity(Var v) {
	getSolver().varBumpActivity(v);
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

void PCSolver::setModSolver(ModSolver* m) {
	getFactory().setModSolver(m);
}

Var PCSolver::newVar() {
	auto v = getParent().getNewVar(); // NOTE: request from the parent remapper TODO prevent remapper from not being used
	add(v);
	return v;
}

int	PCSolver::newSetID(){
	assert(!isParsing());
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

bool PCSolver::symmetryPropagationOnAnalyze(const Lit& p) {
	return getEventQueue().symmetryPropagationOnAnalyze(p);
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

void PCSolver::createVar(Var v, bool nondecision) {
	assert(v>-1);

	bool newvar = v>=nVars();

	while (((uint64_t) v) >= nVars()) {
#ifdef USEMINISAT22
		getSolver().newVar(
				modes().polarity == POL_TRUE ? l_True : modes().polarity == POL_FALSE ? l_False : l_Undef, false);
#else
		getSolver().newVar(true, false);
#endif
	}

	if(newvar){
		getSolver().setDecisionVar(v, not nondecision);
		getEventQueue().notifyVarAdded();
		if (isInitialized()) { //Lazy init
			propagations.resize(nVars(), NULL);
		}
	}
}

int	PCSolver::getTime(const Var& var) const{
	return trail->getTime(mkPosLit(var));
}

void PCSolver::finishParsing(bool& unsat) {
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

	unsat |= getFactory().finishParsing()==SATVAL::UNSAT;
	getEventQueue().finishParsing(unsat);
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
	if (isBeingMonitored()) {
		InnerBacktrack backtrack(untillevel);
		notifyMonitor(backtrack);
	}

	trail->notifyBacktrack(untillevel);
	getEventQueue().notifyBacktrack(untillevel, decision);
}

bool PCSolver::propagateSymmetry2() {
	return getEventQueue().checkSymmetryAlgo2();
}

bool PCSolver::propagateSymmetry(const Lit& l) {
	return getEventQueue().checkSymmetryAlgo1(l);
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

Var PCSolver::changeBranchChoice(const Var& chosenvar) {
	return getEventQueue().notifyBranchChoice(chosenvar);
}

int PCSolver::getNbModelsFound() const {
	return getParent().getNbModelsFound();
}

/*
 * Possible answers:
 * true => satisfiable, at least one model exists (INDEPENDENT of the number of models requested or found)
 * false => unsatisfiable
 *
 * Possible tasks:
 * do propagation => do not do search, do not save any model
 * check satisfiability => save the first model
 * find n/all models and print them => do not save models, but print them one at a time
 * find n/all models and return them => save all models
 * count the number of models => do not save models
 */
bool PCSolver::solve(const litlist& assumptions, const ModelExpandOptions& options) {
	if (optim != Optim::NONE && options.nbmodelstofind != 1) {
		throw idpexception("Finding multiple models can currently not be combined with optimization.\n");
	}

	vec<Lit> vecassumptions;
	for(auto i=assumptions.cbegin(); i!=assumptions.cend(); ++i){
		vecassumptions.push(*i);
	}

	if (options.search == PROPAGATE) { //Only do unit propagation
		return getSolver().solve(vecassumptions, true);
	}

	printSearchStart(clog, verbosity());

	if (optim != Optim::NONE) {
		findOptimal(assumptions, options);
	} else {
		bool moremodels = findNext(vecassumptions, options);
		if (!moremodels) {
			if (getNbModelsFound() == 0) {
				printNoModels(clog, verbosity());
			} else {
				printNoMoreModels(clog, verbosity());
			}
		}
	}

	printSearchEnd(clog, verbosity());

	return getNbModelsFound() > 0;
}

void PCSolver::extractLitModel(InnerModel* fullmodel) {
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

void PCSolver::extractVarModel(InnerModel* fullmodel) {
	fullmodel->varassignments.clear();
	getFactory().includeCPModel(fullmodel->varassignments);
#ifdef CPSUPPORT
	if(hasCPSolver()) {
		getCPSolver().getVariableSubstitutions(fullmodel->varassignments);
	}
#endif
}

/**
 * Checks satisfiability of the theory.
 * Returns false if no model was found, true otherwise.
 * If a model is found, it is printed and returned in <m>, the theory is extended to prevent
 * 		the same model from being found again and
 * 		the datastructures are reset to prepare to find the next model
 */
/**
 * Important: assmpt are the first DECISIONS that are made. So they are not automatic unit propagations
 * and can be backtracked!
 */
bool PCSolver::findNext(const vec<Lit>& assmpt, const ModelExpandOptions& options) {
	bool moremodels = true;
	while (moremodels && (options.nbmodelstofind == 0 || getParent().getNbModelsFound() < options.nbmodelstofind)) {
		bool modelfound = getSolver().solve(assmpt);

		if (!modelfound) {
			moremodels = false;
			break;
		}

		InnerModel* fullmodel = new InnerModel();
		extractLitModel(fullmodel);
		extractVarModel(fullmodel);
		getParent().addModel(*fullmodel);

#ifdef CPSUPPORT
		if(hasCPSolver()) {
			//Check for more models with different var assignment
			while(moremodels && (options.nbmodelstofind == 0 || getParent().getNbModelsFound() < options.nbmodelstofind)) {
				rClause confl = getCPSolver().findNextModel();
				if(confl!=nullPtrClause) {
					moremodels = false;
				} else {
					extractVarModel(fullmodel);
					getParent().addModel(*fullmodel);
				}
			}
		}
#endif

		delete fullmodel;

		//Invalidate SAT model
		if (getSolver().decisionLevel() != assmpt.size()) { //choices were made, so other models possible
			InnerDisjunction invalidation;
			invalidate(invalidation);
			moremodels = invalidateModel(invalidation)==SATVAL::POS_SAT;
		} else {
			moremodels = false;
		}
	}

	return moremodels;
}

void PCSolver::invalidate(InnerDisjunction& clause) {
	// Add negation of model as clause for next iteration.
	// By default: by adding all choice literals
	litlist& invalidation = clause.literals;
	if (!state_savingclauses || getSolver().decisionLevel() > 1) {
		vector<Lit> v = getSolver().getDecisions();
		for (vector<Lit>::const_iterator i = v.cbegin(); i < v.cend(); ++i) {
			invalidation.push_back(~(*i));
		}
	} else {
		//FIXME Currently, unit clauses cannot be state-saved, so if there is only one literal in the whole theory, it might go wrong
		for (uint64_t var = 0; var < nVars(); ++var) {
			invalidation.push_back(value(var) == l_True ? mkLit(var, true) : mkLit(var, false));
		}
	}
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
SATVAL PCSolver::invalidateModel(InnerDisjunction& clause) {
	getSolver().cancelUntil(0); // Otherwise, clauses cannot be added to the sat-solver anyway

	if (state_savingclauses && clause.literals.size() == 1) {
		throw idpexception("Cannot state-save unit clauses at the moment!\n");
	}

	if (modes().verbosity >= 3) {
		clog << "Adding model-invalidating clause: [ ";
		MinisatID::print(clause);
		clog << "]\n";
	}

	if (state_savingclauses) {
		rClause newclause;
		getFactory().add(clause, newclause);
		if (satState()==SATVAL::POS_SAT) {
			state_savedclauses.push_back(newclause);
		}
	} else {
		add(clause);
	}

	return satState();
}

// OPTIMIZATION METHODS

bool PCSolver::invalidateSubset(litlist& invalidation, vec<Lit>& assmpt) {
	int subsetsize = 0;

	for (int i = 0; i < to_minimize.size(); ++i) {
		if (getSolver().model[(vsize)var(to_minimize[i])] == l_True) {
			invalidation.push_back(~to_minimize[i]);
			++subsetsize;
		} else {
			assmpt.push(~to_minimize[i]);
		}
	}

	if (subsetsize == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

bool PCSolver::invalidateValue(litlist& invalidation) {
	bool currentoptimumfound = false;

	for (int i = 0; !currentoptimumfound && i < to_minimize.size(); ++i) {
		if (!currentoptimumfound && getSolver().model[var(to_minimize[i])] == l_True) {
			if (modes().verbosity >= 1) {
				clog << "> Current optimum found for: ";
				getParent().printLiteral(cerr, to_minimize[i]);
				clog << "\n";
			}
			currentoptimumfound = true;
		}
		if (!currentoptimumfound) {
			invalidation.push_back(to_minimize[i]);
		}
	}

	if (invalidation.size() == 0) {
		return true; //optimum has already been found!!!
	} else {
		return false;
	}
}

/*
 * If the optimum possible value is reached, the model is not invalidated. Otherwise, unsat has to be found first, so it is invalidated.
 * TODO: add code that allows to reset the solver when the optimal value has been found, to search for more models with the same optimal value.
 * Borrow this code from savestate/resetstate/saveclauses for the modal solver
 *
 * Returns true if an optimal model was found
 */
bool PCSolver::findOptimal(const litlist& assmpt, const ModelExpandOptions& options) {
	vec<Lit> currentassmpt;
	for(auto i=assmpt.cbegin(); i!=assmpt.cend(); ++i){
		currentassmpt.push(*i);
	}

	bool modelfound = false, unsatreached = false;

	InnerModel* m = new InnerModel();
	while (!unsatreached) {
		if (optim == Optim::AGG) {
			// NOTE: necessary to propagate the changes to the bound correctly
			if(agg_to_minimize->reInitializeAgg() == SATVAL::UNSAT){
				unsatreached = true;
				continue;
			}
		}

		bool sat = getSolver().solve(currentassmpt);
		if (!sat) {
			unsatreached = true;
			break;
		}
		if (sat) {
			modelfound = true;
			//Store current model in m before invalidating the solver
			m->litassignments.clear();
			int nvars = (int) nVars();
			for (int i = 0; i < nvars; ++i) {
				if (value(i) == l_True) {
					m->litassignments.push_back(mkLit(i, false));
				} else if (value(i) == l_False) {
					m->litassignments.push_back(mkLit(i, true));
				}
			}

			//invalidate the solver
			InnerDisjunction invalidation;
			switch (optim) {
			case Optim::LIST:
				unsatreached = invalidateValue(invalidation.literals);
				break;
			case Optim::SUBSET:
				currentassmpt.clear();
				unsatreached = invalidateSubset(invalidation.literals, currentassmpt);
				break;
			case Optim::AGG:
				unsatreached = invalidateAgg(invalidation.literals);
				break;
			case Optim::NONE:
				assert(false);
				break;
			}

			if (!unsatreached) {
				if (getSolver().decisionLevel() != currentassmpt.size()) { //choices were made, so other models possible
					unsatreached = invalidateModel(invalidation) == SATVAL::UNSAT;
				} else {
					unsatreached = true;
				}
			}

			getParent().addModel(*m);
		}
	}

	if (unsatreached && modelfound) {
		getParent().notifyOptimalModelFound();
	}

	return modelfound && unsatreached;
}

bool PCSolver::invalidateAgg(litlist& invalidation) {
	assert(isInitialized());
	auto agg = agg_to_minimize;
	auto s = agg->getSet();
	Weight value = s->getType().getValue(*s);

	printCurrentOptimum(value);
	if(modes().verbosity>=1){
		clog <<"> Current optimal value " <<value <<"\n";
	}

	agg->setBound(AggBound(agg->getSign(), value - 1));

	if (s->getType().getMinPossible(*s) == value) {
		return true;
	}

	HeadReason ar(*agg, createNegativeLiteral(var(agg->getHead())));
	s->getProp()->getExplanation(invalidation, ar);

	return false;
}

void PCSolver::addOptimization(Optim type, const litlist& literals) {
	if (optim != Optim::NONE) {
		throw idpexception(">> Only one optimization statement is allowed.\n");
	}

	optim = type;
	to_minimize = literals;
}

void PCSolver::addAggOptimization(TypedSet* aggmnmz) {
	if (optim != Optim::NONE) {
		throw idpexception(">> Only one optimization statement is allowed.\n");
	}

	optim = Optim::AGG;
	agg_to_minimize = aggmnmz->getAgg().front();
}

void PCSolver::saveState() {
	state_savedlevel = getCurrentDecisionLevel();
	state_savingclauses = true;
}

void PCSolver::resetState() {
	backtrackTo(state_savedlevel);
	assert(state_savedlevel == getCurrentDecisionLevel());
	state_savingclauses = false;
#warning RESET STATE INCORRECT
	//getSolver().removeClauses(state_savedclauses);
	state_savedclauses.clear();
	//getSolver().removeAllLearnedClauses();

}

// PRINT METHODS

void PCSolver::printEnqueued(const Lit& p) const {
	clog << "> Enqueued " << p << " in solver " << getID() << "\n";
}

void PCSolver::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		clog << "> Choice literal, dl " << level << ", in solver " << getID() << ": " << l << ".\n";
	}
}

void PCSolver::printStatistics() const {
	getSolver().printStatistics();
	getEventQueue().printStatistics();
}

void PCSolver::printState() const {
	MinisatID::print(searchengine);
	getEventQueue().printState();
}

void PCSolver::printClause(rClause clause) const {
	getSolver().printClause(getClauseRef(clause));
}

void PCSolver::printCurrentOptimum(const Weight& value) const {
	getParent().printCurrentOptimum(value);
}

// TODO move this to an event in the queue?
// @pre: decision level = 0
void PCSolver::printTheory(ostream& stream){
	assert(getCurrentDecisionLevel()==0);
	stream <<"p ecnf\n";
	std::set<Var> printedvars;
	getSATSolver()->printECNF(stream, printedvars);
	getParent().printTranslation(stream, printedvars);
	clog <<"Currently not printing out any other constructs than clauses from the theory.";
}
