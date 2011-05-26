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
#include "wrapper/InterfaceImpl.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

bool PCSolver::headerunprinted = true;

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes, MinisatID::WrapperPimpl& inter) :
		LogicSolver(modes, inter),
		searchengine(new Solver(*this)),
		state(THEORY_PARSING),
		nbskipped(0),
		optim(NONE), head(-1),
		state_savedlevel(0), state_savingclauses(false){
}

PCSolver::~PCSolver() {
}

lbool PCSolver::value(Var x)	const { return getSolver()->value(x); }
lbool PCSolver::value(Lit p)	const { return getSolver()->value(p); }
uint64_t PCSolver::nVars()		const { return getSolver()->nbVars(); }

rClause PCSolver::createClause(const vec<Lit>& lits, bool learned) {
	return getSolver()->makeClause(lits, learned);
}

void PCSolver::addLearnedClause(rClause c) {
	getSolver()->addLearnedClause(c);
}

void PCSolver::backtrackTo(int level) {
	getSolver()->cancelUntil(level);
}

void PCSolver::setTrue(Lit p, Propagator* module, rClause c) {
	propagations[var(p)] = module;
	getSolver()->uncheckedEnqueue(p, c);
}

int PCSolver::getCurrentDecisionLevel() const {
	return getSolver()->decisionLevel();
}

int PCSolver::getLevel(int var) const {
	return getSolver()->getLevel(var);
}

const vec<Lit>& PCSolver::getTrail() const {
	return getSolver()->getTrail();
}

int PCSolver::getStartLastLevel() const {
	return getSolver()->getStartLastLevel();
}

int PCSolver::getNbDecisions() const {
	return getSolver()->decisionLevel();
}

vector<Lit> PCSolver::getDecisions() const {
	return getSolver()->getDecisions();
}

bool PCSolver::totalModelFound() {
	return getSolver()->totalModelFound();
}

void PCSolver::varBumpActivity(Var v) {
	getSolver()->varBumpActivity(v);
}

//IMPORTANT: only allowed after initialization!
Var PCSolver::newVar() {
	assert(isInitialized());
	Var v = nVars();
	add(v);
	return v;
}

// Given a two-valued model, check that it satisfies all constraints (e.g. wellfoundedness-check). If pass, return l_True, otherwise l_False
//if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status
lbool PCSolver::checkStatus(lbool status) const {
	return getEventQueue().notifyFullAssignmentFound();
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(Lit l) {
	return getEventQueue().getExplanation(l);
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

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolver::newDecisionLevel() {
	getEventQueue().notifyNewDecisionLevel();
}

void PCSolver::backtrackDecisionLevel(int levels, int untillevel) {
	if(isBeingMonitored()){
		InnerBacktrack backtrack(untillevel);
		notifyMonitor(backtrack);
	}

	getEventQueue().notifyBacktrack(levels, untillevel);
}

/**
 * Returns not-owning pointer
 *
 * During initialization, store the propagations to redo them later on.
 */
rClause PCSolver::propagate(Lit l) {
	//TODO fix initialization order and printing of it
	if(isBeingMonitored()){
		bool print = false;
		if (!isInitialized()) {
			print = true;
		}else{
			if(nbskipped>initialprops.size()){
				print = true;
			}
			nbskipped++;
		}
		if(print){
			InnerPropagation prop;
			prop.decisionlevel = getCurrentDecisionLevel();
			prop.propagation = l;
			notifyMonitor(prop);
		}
	}

	if (!isInitialized()) {
		initialprops.push_back(l);
		return nullPtrClause;
	}

	return getEventQueue().notifyPropagate(l);
}

// NOTE the sat solver calls this simplify, not his own!
bool PCSolver::simplify() {
	/*bool simp = getSolver()->simplify();
	for(solverlist::const_iterator i=getPropagators().begin(); simp && i<getPropagators().end(); ++i){
		if((*i)->present){
			simp = (*i)->get()->simplify();
		}
	}
	return simp;*/
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
		return getSolver()->solve(assumptions, true);
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
	if(hasCPSolver()){
#ifdef CPSUPPORT
		getCPSolver()->getVariableSubstitutions(fullmodel->varassignments);
#endif
	}
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
		bool modelfound = getSolver()->solve(assmpt);

		if (!modelfound) {
			moremodels = false;
			break;
		}

		InnerModel* fullmodel = new InnerModel();
		extractLitModel(fullmodel);
		extractVarModel(fullmodel);
		getParent().addModel(*fullmodel);

		//Check for more models with different var assignment
		if(hasCPSolver()){
#ifdef CPSUPPORT
			while(moremodels && (options.nbmodelstofind == 0 || getParent().getNbModelsFound() < options.nbmodelstofind)){
				rClause confl = getCPSolver()->findNextModel();
				if(confl!=nullPtrClause){
					moremodels = false;
				}else{
					extractVarModel(fullmodel);
					getParent().addModel(*fullmodel);
				}
			}
#endif
		}
		delete fullmodel;

		//Invalidate SAT model
		if (getSolver()->decisionLevel() != assmpt.size()) { //choices were made, so other models possible
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
	if(!state_savingclauses || getSolver()->decisionLevel()>1){
		vector<Lit> v = getSolver()->getDecisions();
		for (vector<Lit>::const_iterator i = v.begin(); i < v.end(); ++i) {
			invalidation.push(~(*i));
		}
	}else{
		//FIXME Currently, unit clauses cannot be state-saved, so if there is only one literal in the whole theory, it might go wrong
		for (int var = 0; var<nVars(); ++var) {
			invalidation.push(value(var)==l_True?mkLit(var, true):mkLit(var, false));
		}
	}
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
bool PCSolver::invalidateModel(InnerDisjunction& clause) {
	getSolver()->cancelUntil(0); // Otherwise, clauses cannot be added to the sat-solver anyway

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
		result = add(clause, newclause);
		if(result){
			state_savedclauses.push_back(newclause);
		}
	}else{
		result = add(clause);
	}

	getSolver()->varDecayActivity();
	getSolver()->claDecayActivity();

	return result;
}

// OPTIMIZATION METHODS

bool PCSolver::invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt) {
	int subsetsize = 0;

	for (int i = 0; i < to_minimize.size(); ++i) {
		if (getSolver()->model[var(to_minimize[i])] == l_True) {
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

	for (int i = 0; !currentoptimumfound && i < to_minimize.size(); ++i) {
		if (!currentoptimumfound && getSolver()->model[var(to_minimize[i])] == l_True) {
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
		rslt = getSolver()->solve(assmpt);
		if(!rslt){
			getSolver()->cancelUntil(0);
			vec<Lit> lits;
			lits.push(~to_minimize[0]);
			getSolver()->addClause(lits);
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
			assert(getAggSolver()!=NULL);
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			getAggSolver()->propagateMnmz();
		}

		bool sat = getSolver()->solve(currentassmpt);
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
				unsatreached = getAggSolver()->invalidateAgg(invalidation.literals);
				break;
			case NONE:
				assert(false);
				break;
			}

			if (!unsatreached) {
				if (getSolver()->decisionLevel() != currentassmpt.size()) { //choices were made, so other models possible
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

void PCSolver::saveState(){
	state_savedlevel = getCurrentDecisionLevel();
	state_savingclauses = true;
}

void PCSolver::resetState(){
	backtrackTo(state_savedlevel);
	assert(state_savedlevel == getCurrentDecisionLevel());
	state_savingclauses = false;
#warning RESET STATE INCORRECT
	//getSolver()->removeClauses(state_savedclauses);
	state_savedclauses.clear();
	//getSolver()->removeAllLearnedClauses();

}

// PRINT METHODS

string PCSolver::getModID() const {
	stringstream ss;
	if(hasModSolver()){
		ss <<getModSolver()->getPrintId();
	}
	return ss.str();
}

void PCSolver::printEnqueued(const Lit& p) const{
	clog <<"> Enqueued " <<p;
	if(hasModSolver()){
		clog <<" in modal solver " <<getModID();
	}
	reportf("\n");
}

void PCSolver::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		clog <<"> Choice literal, dl " <<level <<", ";
		if(hasModSolver()){
			clog <<" in modal solver " <<getModID();
		}

		clog <<": " <<l <<".\n";
	}
}

void PCSolver::printStatistics() const {
	getSolver()->printStatistics();
	for(solverlist::const_iterator i=getPropagators().begin(); i<getPropagators().end(); ++i){
		if((*i)->present){
			(*i)->get()->printStatistics();
		}
	}
}

void PCSolver::printState() const{
	MinisatID::print(getSolver());
	for(vector<WrappedPropagator*>::const_iterator i=getPropagators().begin(); i<getPropagators().end(); ++i){
		(*i)->get()->printState();
	}
}

void PCSolver::printClause(rClause clause) const {
	getSolver()->printClause(getClauseRef(clause));
}

void PCSolver::printCurrentOptimum(const Weight& value) const{
	getParent().printCurrentOptimum(value);
}
