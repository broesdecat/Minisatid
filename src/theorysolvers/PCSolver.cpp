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
#include "modules/AggSolver.hpp"
#include "modules/CPSolver.hpp"
#include "wrapper/InterfaceImpl.hpp"

#include "theorysolvers/PropagatorFactory.hpp"
#include "theorysolvers/EventQueue.hpp"

#include "monitors/SearchMonitor.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes, MinisatID::WrapperPimpl& inter, int ID) :
		LogicSolver(modes, inter),
		ID(ID),
		searchengine(NULL),
#ifdef CPSUPPORT //TODO create dummy implemententation of CPSolver to remove all the ifdefs
		cpsolver(NULL),
#endif
		queue(NULL),
		factory(NULL),
		state(THEORY_PARSING),
		optim(NONE), head(-1),
		state_savedlevel(0), state_savingclauses(false),
		searchmonitor(new SearchMonitor()){

	queue = new EventQueue(*this);

	searchengine = createSolver(this);
#ifdef CPSUPPORT
	cpsolver = new CPSolver(this);
#endif

	factory = new PropagatorFactory(modes, this);
}

PCSolver::~PCSolver() {
	delete(queue);
	delete(searchengine);
#ifdef CPSUPPORT
	delete(cpsolver);
#endif
	delete(factory);
	delete(searchmonitor);
}

#ifdef CPSUPPORT
bool PCSolver::hasCPSolver() const {
	return cpsolver!=NULL && cpsolver->isPresent();
}
#endif

lbool PCSolver::value(Var x)	const { return getSolver().value(x); }
lbool PCSolver::value(Lit p)	const { return getSolver().value(p); }
uint64_t PCSolver::nVars()		const { return getSolver().nbVars(); }

void PCSolver::notifyNonDecisionVar(Var var){
	getSATSolver()->setDecisionVar(var, false);
}

rClause PCSolver::createClause(const vec<Lit>& lits, bool learned) {
	if(lits.size()==0){
		vec<Lit> dummylits; //INVAR, solver does not simplify learned clauses
		dummylits.push(mkLit(dummy1, true));
		dummylits.push(mkLit(dummy2, true));
		return getSolver().makeClause(dummylits, learned);
	}else if(lits.size()==1){
		vec<Lit> dummylits;
		dummylits.push(lits[0]);
		dummylits.push(mkLit(dummy1, true));
		return getSolver().makeClause(dummylits, learned);
	}else{
		return getSolver().makeClause(lits, learned);
	}
}

void PCSolver::addLearnedClause(rClause c) { getSolver().addLearnedClause(c); }
void PCSolver::removeClause(rClause c) { getSolver().removeClause(c); }
int	PCSolver::getClauseSize	(rClause cr) const { return getSATSolver()->getClauseSize(cr); }
Lit	PCSolver::getClauseLit	(rClause cr, int i) const { return getSATSolver()->getClauseLit(cr, i); }

void PCSolver::backtrackTo(int level) {
	getSolver().cancelUntil(level);
}

void PCSolver::setTrue(const Lit& p, Propagator* module, rClause c) {
	propagations[var(p)] = module;
	getSolver().uncheckedEnqueue(p, c);
}

void PCSolver::notifySetTrue(const Lit& p) {
	getEventQueue().setTrue(p);

	if(isBeingMonitored()){
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

const vec<Lit>& PCSolver::getTrail() const {
	return getSolver().getTrail();
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

bool PCSolver::isAlreadyUsedInAnalyze(const Lit& lit) const{
	return getSolver().isAlreadyUsedInAnalyze(lit);
}

bool PCSolver::totalModelFound() {
	return getSolver().totalModelFound();
}

void PCSolver::varBumpActivity(Var v) {
	getSolver().varBumpActivity(v);
}

void PCSolver::accept(Propagator* propagator){
	getEventQueue().accept(propagator);
}

void PCSolver::accept(Propagator* propagator, EVENT event){
	getEventQueue().accept(propagator, event);
}

void PCSolver::acceptLitEvent(Propagator* propagator, const Lit& lit, PRIORITY priority){
	getEventQueue().acceptLitEvent(propagator, lit, priority);
}

void PCSolver::acceptFinishParsing(Propagator* propagator, bool late){
	getEventQueue().acceptFinishParsing(propagator, late);
}

void PCSolver::setModSolver(ModSolver* m){
	getFactory().setModSolver(m);
}

//IMPORTANT: only allowed after parsing!
Var PCSolver::newVar() {
	assert(!isParsing());
	Var newvar = nVars()+1;
	createVar(newvar);
	return newvar;
}

rClause PCSolver::checkFullAssignment() {
	return getEventQueue().notifyFullAssignmentFound();
}

void PCSolver::notifyClauseAdded(rClause clauseID){
	getEventQueue().notifyClauseAdded(clauseID);
}

void PCSolver::notifyClauseDeleted(rClause clauseID){
	getEventQueue().notifyClauseDeleted(clauseID);
}

bool PCSolver::symmetryPropagationOnAnalyze(const Lit& p){
	return getEventQueue().symmetryPropagationOnAnalyze(p);
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(const Lit& l) {
	if (modes().verbosity > 2) {
		clog <<"Generating explanation for " <<l <<", ";
	}

	Propagator* propagator = propagations[var(l)];
	assert(propagator!=NULL); //If this happens, there is usually an error in the generated explanations!

	if (modes().verbosity > 2) {
		clog <<"Generated by " <<propagator->getName() <<": ";
	}

	rClause explan = propagator->getExplanation(l);
	assert(explan!=nullPtrClause);

	if (verbosity() > 2) {
		print(explan, *this);
		clog <<"\n";
	}

	return explan;
}

/* complexity O(#propagations on level)
 * @pre: p has been assigned in the current decision level!
 * Returns true if l was asserted before p
 */
bool PCSolver::assertedBefore(const Var& l, const Var& p) const {
	if(getLevel(l) < getLevel(p)){
		return true;
	}

	bool before = true;
	const vec<Lit>& trail = getTrail();
		int recentindex = getStartLastLevel();
		for (int i = recentindex; i < trail.size(); ++i) {
			Lit rlit = trail[i];
		if (var(rlit) == l) { // l encountered first, so before
			break;
		}
		if (var(rlit) == p) { // p encountered first, so after
			before = false;
			break;
		}
	}

	return before;
}

void PCSolver::createVar(Var v){
	assert(v>-1);

	while (((uint64_t) v) >= nVars()) {
#ifdef USEMINISAT22
		getSolver().newVar(modes().polarity==POL_TRUE?l_True:modes().polarity==POL_FALSE?l_False:l_Undef, false);
#else
		getSolver().newVar(true, false);
#endif
	}

	getSolver().setDecisionVar(v, true);

	getEventQueue().notifyVarAdded();

	getSearchMonitor().addCount(v);

	if (isInitialized()) { //Lazy init
		propagations.resize(nVars(), NULL);
	}
}

void PCSolver::finishParsing(bool& unsat) {
	state = THEORY_INITIALIZING;

	dummy1 = newVar();
	InnerDisjunction d1;
	d1.literals.push(mkLit(dummy1, false));
	add(d1);
	dummy2 = newVar();
	InnerDisjunction d2;
	d2.literals.push(mkLit(dummy2, false));
	add(d2);

	propagations.resize(nVars(), NULL); //Lazy init

	getFactory().finishParsing();
	getEventQueue().finishParsing(unsat);
	if(modes().useaggheur){
		getSATSolver()->notifyCustomHeur();
	}

	// Aggregate pre processing idea
	//if(aggsolverpresent){
	//getAggSolver()->findClausalPropagations();
	//}

	state = THEORY_INITIALIZED;
}

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolver::newDecisionLevel() {
	getEventQueue().notifyNewDecisionLevel();
}

void PCSolver::backtrackDecisionLevel(int untillevel, const Lit& decision) {
	if(isBeingMonitored()){
		InnerBacktrack backtrack(untillevel);
		notifyMonitor(backtrack);
	}

	getEventQueue().notifyBacktrack(untillevel, decision);
}

/**
 * Returns not-owning pointer
 *
 * During initialization, store the propagations to redo them later on.
 */
rClause PCSolver::propagate() {
	return getEventQueue().notifyPropagate();
}

int	PCSolver::getNbOfFormulas() const{
	return getEventQueue().getNbOfFormulas();
}

Var PCSolver::changeBranchChoice(const Var& chosenvar){
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
bool PCSolver::solve(const vec<Lit>& assumptions, const ModelExpandOptions& options){
	if(optim!=NONE && options.nbmodelstofind!=1){
		throw idpexception("Finding multiple models can currently not be combined with optimization.\n");
	}

	if(options.search==PROPAGATE){ //Only do unit propagation
		return getSolver().solve(assumptions, true);
	}

	printSearchStart(clog, verbosity());

	if(optim!=NONE){
		findOptimal(assumptions, options);
	}else{
		bool moremodels = findNext(assumptions, options);
		if(!moremodels){
			if(getNbModelsFound()==0){
				printNoModels(clog, verbosity());
			}else{
				printNoMoreModels(clog, verbosity());
			}
		}
	}

	printSearchEnd(clog, verbosity());

	return getNbModelsFound()>0;
}

void PCSolver::extractLitModel(InnerModel* fullmodel){
	fullmodel->litassignments.clear();
	// FIXME implement more efficiently in the satsolver?
	for (uint64_t i = 0; i < nVars(); ++i) {
		if (value(i) == l_True) {
			fullmodel->litassignments.push(mkLit(i, false));
		} else if (value(i) == l_False) {
			fullmodel->litassignments.push(mkLit(i, true));
		}
	}
}

void PCSolver::extractVarModel(InnerModel* fullmodel){
	fullmodel->varassignments.clear();
#ifdef CPSUPPORT
	if(hasCPSolver()){
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
		if(hasCPSolver()){
			//Check for more models with different var assignment
			while(moremodels && (options.nbmodelstofind == 0 || getParent().getNbModelsFound() < options.nbmodelstofind)){
				rClause confl = getCPSolver().findNextModel();
				if(confl!=nullPtrClause){
					moremodels = false;
				}else{
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
			moremodels = invalidateModel(invalidation);
		} else {
			moremodels = false;
		}
	}

	return moremodels;
}

void PCSolver::invalidate(InnerDisjunction& clause) {
	// Add negation of model as clause for next iteration.
	// By default: by adding all choice literals
	vec<Lit>& invalidation = clause.literals;
	if(!state_savingclauses || getSolver().decisionLevel()>1){
		vector<Lit> v = getSolver().getDecisions();
		for (vector<Lit>::const_iterator i = v.begin(); i < v.end(); ++i) {
			invalidation.push(~(*i));
		}
	}else{
		//FIXME Currently, unit clauses cannot be state-saved, so if there is only one literal in the whole theory, it might go wrong
		for (uint64_t var = 0; var<nVars(); ++var) {
			invalidation.push(value(var)==l_True?mkLit(var, true):mkLit(var, false));
		}
	}
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
bool PCSolver::invalidateModel(InnerDisjunction& clause) {
	getSolver().cancelUntil(0); // Otherwise, clauses cannot be added to the sat-solver anyway

	if(state_savingclauses && clause.literals.size() == 1){
		throw idpexception("Cannot state-save unit clauses at the moment!\n");
	}

	if (modes().verbosity >= 3) {
		clog <<"Adding model-invalidating clause: [ ";
		MinisatID::print(clause);
		clog <<"]\n";
	}

	bool result;
	if(state_savingclauses){
		rClause newclause;
		result = getFactory().add(clause, newclause);
		if(result){
			state_savedclauses.push_back(newclause);
		}
	}else{
		result = add(clause);
	}

	getSolver().varDecayActivity();
	getSolver().claDecayActivity();

	return result;
}

// OPTIMIZATION METHODS

bool PCSolver::invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt) {
	int subsetsize = 0;

	for (unsigned int i = 0; i < to_minimize.size(); ++i) {
		if (getSolver().model[var(to_minimize[i])] == l_True) {
			invalidation.push(~to_minimize[i]);
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

bool PCSolver::invalidateValue(vec<Lit>& invalidation) {
	bool currentoptimumfound = false;

	for (unsigned int i = 0; !currentoptimumfound && i < to_minimize.size(); ++i) {
		if (!currentoptimumfound && getSolver().model[var(to_minimize[i])] == l_True) {
			if (modes().verbosity >= 1) {
				clog <<"> Current optimum found for: ";
				getParent().printLiteral(cerr, to_minimize[i]);
				clog <<"\n";
			}
			currentoptimumfound = true;
		}
		if (!currentoptimumfound) {
			invalidation.push(to_minimize[i]);
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
bool PCSolver::findOptimal(const vec<Lit>& assmpt, const ModelExpandOptions& options) {
	vec<Lit> currentassmpt;
	assmpt.copyTo(currentassmpt);

	bool modelfound = false, unsatreached = false;

	//CHECKS whether first element yields a solution, otherwise previous strategy is done
	//should IMPLEMENT dichotomic search in the end: check half and go to interval containing solution!
	/*
	if(optim==MNMZ){
		assmpt.push(to_minimize[0]);
		rslt = getSolver().solve(assmpt);
		if(!rslt){
			getSolver().cancelUntil(0);
			vec<Lit> lits;
			lits.push(~to_minimize[0]);
			getSolver().addClause(lits);
			assmpt.pop();
			rslt = true;
		}else{
			optimumreached = true;
			m.clear();
			int nvars = (int) nVars();
			for (int i = 0; i < nvars; ++i) {
				if (value(i) == l_True) {
					m.push(mkLit(i, false));
				} else if (value(i) == l_False) {
					m.push(mkLit(i, true));
				}
			}
		}
	}*/

	InnerModel* m = new InnerModel();
	while (!unsatreached) {
		if (optim == AGGMNMZ) {
			assert(getFactory().getOptimAggSolver()!=NULL);
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			getFactory().getOptimAggSolver()->propagateMnmz();
		}

		bool sat = getSolver().solve(currentassmpt);
		if(!sat){
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
					m->litassignments.push(mkLit(i, false));
				} else if (value(i) == l_False) {
					m->litassignments.push(mkLit(i, true));
				}
			}

			//invalidate the solver
			InnerDisjunction invalidation;
			switch (optim) {
			case MNMZ:
				unsatreached = invalidateValue(invalidation.literals);
				break;
			case SUBSETMNMZ:
				currentassmpt.clear();
				unsatreached = invalidateSubset(invalidation.literals, currentassmpt);
				break;
			case AGGMNMZ:
				unsatreached = getFactory().getOptimAggSolver()->invalidateAgg(invalidation.literals);
				break;
			case NONE:
				assert(false);
				break;
			}

			if (!unsatreached) {
				if (getSolver().decisionLevel() != currentassmpt.size()) { //choices were made, so other models possible
					unsatreached = !invalidateModel(invalidation);
				} else {
					unsatreached = true;
				}
			}

			getParent().addModel(*m);
		}
	}

	if(unsatreached && modelfound){
		getParent().notifyOptimalModelFound();
	}

	return modelfound && unsatreached;
}

void PCSolver::addOptimization(Optim type, Var head) {
	if (optim != NONE) { throw idpexception(">> Only one optimization statement is allowed.\n"); }

	optim = type;
	this->head = head;
}

void PCSolver::addOptimization(Optim type, const vec<Lit>& literals){
	if (optim != NONE) { throw idpexception(">> Only one optimization statement is allowed.\n"); }

	optim = type;
	literals.copyTo(to_minimize);
}

void PCSolver::saveState(){
	state_savedlevel = getCurrentDecisionLevel();
	state_savingclauses = true;
}

void PCSolver::resetState(){
	backtrackTo(state_savedlevel);
	assert(state_savedlevel == getCurrentDecisionLevel());
	state_savingclauses = false;
#warning RESET STATE INCORRECT
	//getSolver().removeClauses(state_savedclauses);
	state_savedclauses.clear();
	//getSolver().removeAllLearnedClauses();

}

// PRINT METHODS

void PCSolver::printEnqueued(const Lit& p) const{
	clog <<"> Enqueued " <<p <<" in solver " <<getID() <<"\n";
}

void PCSolver::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		clog <<"> Choice literal, dl " <<level <<", in solver " <<getID() <<": " <<l <<".\n";
	}
}

void PCSolver::printStatistics() const {
	getSolver().printStatistics();
	getEventQueue().printStatistics();
}

void PCSolver::printState() const{
	MinisatID::print(searchengine);
	getEventQueue().printState();
}

void PCSolver::printClause(rClause clause) const {
	getSolver().printClause(getClauseRef(clause));
}

void PCSolver::printCurrentOptimum(const Weight& value) const{
	getParent().printCurrentOptimum(value);
}
