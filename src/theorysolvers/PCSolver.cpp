/* * Copyright 2007-2011 Katholieke Universiteit Leuven * * Use of this software is governed by the GNU LGPLv3.0 license * * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium */
#include "theorysolvers/PCSolver.hpp"

#include <iostream>

#include "external/InterfaceImpl.hpp"

#include "satsolver/SATSolver.hpp"
#include "modules/IDSolver.hpp"
#include "modules/AggSolver.hpp"
#include "modules/ModSolver.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;
using namespace Minisat;


PCLogger::PCLogger(): propagations(0){
}

void PCLogger::addCount(Var v) {
	if((v+1)>occurrences.size()){
		occurrences.resize(v+1, 0);
	}
	occurrences[v]++;
}

int PCLogger::getCount(Var v) const {
	return v>occurrences.size()?0:occurrences.at(v);
}


DPLLTSolver::~DPLLTSolver() {
	if(createdhere){
		delete module;
	}
}

//Has to be value copy of modes!
PCSolver::PCSolver(SolverOption modes, MinisatID::WLSImpl* inter) :
		LogicSolver(modes, inter),
		satsolver(NULL), idsolver(NULL), aggsolver(NULL), modsolver(NULL),
		initialized(false),
		optim(NONE), head(-1),
		logger(new PCLogger()){
	satsolver = createSolver(*this);

	aggsolver  = new DPLLTSolver(new AggSolver(this), true);
	solvers.push_back(aggsolver);

	idsolver = new DPLLTSolver(new IDSolver(this), true);
	solvers.push_back(idsolver);

	if(modes.printcnfgraph){
		reportf("graph ecnftheory {\n");
	}
}

PCSolver::~PCSolver() {
	deleteList<DPLLTSolver>(solvers);
	delete satsolver;
	delete logger;
}

void PCSolver::setModSolver(pModSolver m) {
	modsolver = new DPLLTSolver(m, false);
	solvers.insert(solvers.begin(), modsolver);
}

IDSolver* PCSolver::getIDSolver() const { return (idsolver==NULL || !idsolver->present)?NULL:dynamic_cast<IDSolver*>(idsolver->get()); }
AggSolver* PCSolver::getAggSolver() const { return (aggsolver==NULL || !aggsolver->present)?NULL:dynamic_cast<AggSolver*>(aggsolver->get()); }
ModSolver* PCSolver::getModSolver() const { return (modsolver==NULL || !modsolver->present)?NULL:dynamic_cast<ModSolver*>(modsolver->get()); }

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

void PCSolver::setTrue(Lit p, DPLLTmodule* module, rClause c) {
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

///////
// INITIALIZING THE THEORY // Add STATE concept to solver to check for correctness
////////

//FIXME: calling this from inside is not allowed during parsing: it breaks the theory that's being read!
Var PCSolver::newVar() {
	assert(initialized);
	Var v = nVars();
	addVar(v);
	return v;
}

void PCSolver::addVar(Var v) {
	assert(v>-1);

	while (((uint64_t) v) >= nVars()) {
		getSolver()->newVar(true, false);
		for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){
			if((*i)->present){
				(*i)->get()->notifyVarAdded(nVars());
			}
		}
	}

	getSolver()->setDecisionVar(v, true);
	logger->addCount(v);

	if (initialized) {
		propagations.resize(nVars(), NULL);
	}
}

void PCSolver::addVars(const vec<Lit>& a) {
	for (int i = 0; i < a.size(); i++) {
		addVar(var(a[i]));
	}
}

bool PCSolver::addClause(vec<Lit>& lits) {
	if (modes().verbosity >= 2) {
		clog <<"Adding clause:";
		for (int i = 0; i < lits.size(); i++) {
			clog <<" " <<lits[i];
		}
		clog <<"\n";
	}
	addVars(lits);

	if(modes().printcnfgraph){
		for(int i=0; i<lits.size(); i++){
			if(i>0){ clog <<" -- "; }
			clog <<getPrintableVar(var(lits[i]));
		}
		if(lits.size()>1){ clog <<" -- " <<getPrintableVar(var(lits[0])) <<" "; }
		clog <<"[color=blue];\n";
	}

	return getSolver()->addClause(lits);
}

bool PCSolver::addEquivalence(const Lit& head, const vec<Lit>& rightlits, bool conj) {
	addVar(head);
	addVars(rightlits);
	bool notunsat = true;

	//create the completion
	vec<Lit> comp;
	comp.push(head);

	for (int i = 0; i < rightlits.size(); i++) {
		comp.push(rightlits[i]);
	}

	if (conj) {
		for (int i = 1; i < comp.size(); i++) {
			comp[i] = ~comp[i];
		}
	} else {
		comp[0] = ~comp[0];
	}

	vec<Lit> temp; //because addclause empties temp
	comp.copyTo(temp);
	notunsat = addClause(temp);

	for (int i = 1; notunsat && i < comp.size(); i++) {
		vec<Lit> binclause(2);
		binclause[0] = ~comp[0];
		binclause[1] = ~comp[i];
		notunsat = addClause(binclause);
	}

	return notunsat;
}

bool PCSolver::addRule(bool conj, Lit head, const vec<Lit>& lits) {
	assert(getIDSolver()!=NULL);
	addVar(head);
	addVars(lits);	if (verbosity() >= 2) {		report("Adding %s rule, %d <- ", conj?"conjunctive":"disjunctive", getPrintableVar(var(head)));		for (int i = 0; i < lits.size(); i++) {			report("%s%d ", sign(lits[i])?"-":"",getPrintableVar(var(lits[i])));		}		report("\n");	}
	return getIDSolver()->addRule(conj, head, lits);
}

bool PCSolver::addRuleToID(int defid, bool conj, Lit head, const vec<Lit>& lits){
#warning No multi definition support yet
	throw idpexception("No support yet for adding multiple separate definitions.");
}

bool PCSolver::addSet(int setid, const vec<Lit>& lits) {
	assert(getAggSolver()!=NULL);
	addVars(lits);
	vector<Weight> w;
	w.resize(lits.size(), 1);

	return addSet(setid, lits, w);
}

bool PCSolver::addSet(int setid, const vec<Lit>& lits, const vector<Weight>& w) {
	assert(getAggSolver()!=NULL);
	addVars(lits);
	vector<Lit> ll;	ll.reserve(lits.size());
	for (int i = 0; i < lits.size(); i++) {
		ll.push_back(lits[i]);
	}

	if(modes().printcnfgraph){
		for(int i=0; i<lits.size(); i++){
			if(i>0){ clog <<" -- "; }
			clog <<getPrintableVar(var(lits[i]));
		}
		if(lits.size()>1){ clog <<" -- " <<getPrintableVar(var(lits[0])) <<" "; }
		clog <<"[color=green];\n";
	}

	return getAggSolver()->addSet(setid, ll, w);
}

bool PCSolver::addAggrExpr(Lit head, int setid, const Weight& bound, AggSign boundsign, AggType type, AggSem defined) {
	assert(getAggSolver()!=NULL);
	addVar(head);
	if (sign(head)) {
		throw idpexception("Negative heads are not allowed.\n");
	}
	return getAggSolver()->addAggrExpr(var(head), setid, bound, boundsign, type, defined);
}

bool PCSolver::addIntVar(int groundname, int min, int max) {
	throw idpexception("CP-support is not compiled in.\n");
}

void PCSolver::checkHead(Lit head) {
	addVar(head);
	if (sign(head)) {
		throw idpexception("Negative heads are not allowed.\n");
	}
}

bool PCSolver::addCPBinaryRel(Lit head, int groundname, EqType rel, int bound) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPBinaryRelVar(Lit head, int groundname, EqType rel, int groundname2) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSum(Lit head, vector<int> termnames, EqType rel, int bound) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSum(Lit head, vector<int> termnames, vector<int> mult, EqType rel, int bound) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSumVar(Lit head, vector<int> termnames, EqType rel, int rhstermname) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSumVar(Lit head, vector<int> termnames, vector<int> mult, EqType rel, int rhstermname) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPCount(vector<int> termnames, int value, EqType rel, int rhstermname) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPAlldifferent(const vector<int>& termnames) {
	throw idpexception("CP-support is not compiled in.\n");
}

void PCSolver::addForcedChoices(const vec<Lit>& forcedchoices) {
	if (forcedchoices.size() != 0) {
		getSolver()->addForcedChoices(forcedchoices);
	}
}

/*
 * Returns "false" if UNSAT was already found, otherwise "true"
 */
void PCSolver::finishParsing(bool& present, bool& unsat) {
	present = true;
	unsat = false;

	propagations.resize(nVars(), NULL); //Lazy init	//Notify parsing is over	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){		if((*i)->present){			(*i)->get()->notifyParsed();		}	}

	//IMPORTANT Call definition solvers last for recursive aggregates and rules might be added by other solvers!	//Finish all solvers
	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if((*i)->present){
			(*i)->get()->finishParsing((*i)->present, unsat);
			(*i)->get()->notifyInitialized();
			if(unsat){
				return;
			}
		}
	}	//Propagate all non-propagated literals	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){		if ((*i)->present && !(*i)->get()->simplify()) {			unsat = true; return;		} else if(!(*i)->present) {			if (modes().verbosity > 0) {				clog <<">    (there will be no propagations on " <<(*i)->get()->getName() <<" module)\n";			}		}	}

	// Do all propagations that have already been done on the SAT-solver level.
	initialized = true;
	for (vector<Lit>::const_iterator i=initialprops.begin(); i < initialprops.end(); i++) {
		if (propagate(*i) != nullPtrClause) {
			unsat = true; return;
		}
	}

	if (propagateAtEndOfQueue() != nullPtrClause) {
		unsat = true; return;
	}

	// Aggregate pre processing idea
	/*if(aggsolverpresent){
	 getAggSolver()->findClausalPropagations();
	 }*/

	if(modes().printcnfgraph){
		clog <<"}\n";
	}
}

// IDSOLVER SPECIFIC

void PCSolver::removeAggrHead(Var x) {
	if (getIDSolver()!=NULL) {
		getIDSolver()->removeAggrHead(x);
	}
}

void PCSolver::notifyAggrHead(Var x) {
	if (getIDSolver()!=NULL) {
		getIDSolver()->notifyAggrHead(x);
	}
}

//if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status
lbool PCSolver::checkStatus(lbool status) const {
	if(status==l_True){ //Model found, check model:
		if(getIDSolver()!=NULL && !getIDSolver()->checkStatus()){
			return l_False;
		}

		if(getAggSolver()!=NULL && !getAggSolver()->checkStatus()){
			return l_False;
		}
	}
	return status;
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(Lit l) {
	if (modes().verbosity > 2) {
		clog <<"Find T-theory explanation for " <<l <<"\n";
	}

	DPLLTmodule* solver = propagations[var(l)];
	assert(solver!=NULL); //If this happens, there is usually an error in the generated explanations!

	rClause explan = solver->getExplanation(l);
	assert(explan!=nullPtrClause);

	if (verbosity() >= 2) {
		clog <<"Implicit reason clause from the " <<solver->getName() <<" module ";
		Print::print(l, sign(l) ? l_False : l_True);
		clog <<" : ";
		Print::print(explan, *this);
		clog <<"\n";
	}

	return explan;
}

/*
 * @pre: p has been assigned in the current decision level!
 * Returns true if l was asserted before p
 */
bool PCSolver::assertedBefore(const Var& l, const Var& p) const {
	//Check if level is lower
	if(getLevel(l) < getLevel(p)){
		return true;
	}

	bool before = true;
	const vec<Lit>& trail = getTrail();
		int recentindex = getStartLastLevel();
		for (int i = recentindex; i < trail.size(); i++) {
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

// SAT SOLVER SPECIFIC

void PCSolver::backtrackRest(Lit l) {
/*	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if((*i)->present){
			(*i)->get()->backtrack(l);
		}
	}*/
}

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolver::newDecisionLevel() {
	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if((*i)->present){
			(*i)->get()->newDecisionLevel();
		}
	}
}

void PCSolver::backtrackDecisionLevel(int levels, int untillevel) {
	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if((*i)->present){
			(*i)->get()->backtrackDecisionLevels(levels, untillevel);
		}
	}
}

/**
 * Returns not-owning pointer
 */
rClause PCSolver::propagate(Lit l) {
	if (!initialized) {		initialprops.push_back(l);		return nullPtrClause;	}

	rClause confl = nullPtrClause;
	for(solverlist::const_iterator i=solvers.begin(); confl==nullPtrClause && i<solvers.end(); i++){
		if((*i)->present){
			confl = (*i)->get()->propagate(l);
		}
	}

	return confl;
}

/**
 * Returns not-owning pointer
 */
rClause PCSolver::propagateAtEndOfQueue() {
	if(!initialized){ return nullPtrClause;	}

	rClause confl = nullPtrClause;
	for(solverlist::const_iterator i=solvers.begin(); confl==nullPtrClause && i<solvers.end(); i++){
		if((*i)->present){
			//IMPORTANT: if any solver has made propagations, we go back to unit propagation first!
			int sizebefore = getSolver()->getTrail().size();
			confl = (*i)->get()->propagateAtEndOfQueue();
			int sizeafter = getSolver()->getTrail().size();
			if(sizebefore<sizeafter){
				return confl;
			}
		}
	}
	return confl;
}

/******************
 * SEARCH METHODS *
 ******************/

/**
 * Important: the SATsolver never calls his own simplify, he always goes through the PC solver
 */
bool PCSolver::simplify() {
	bool simp = getSolver()->simplify();
	for(solverlist::const_iterator i=solvers.begin(); simp && i<solvers.end(); i++){
		if((*i)->present){
			simp = (*i)->get()->simplify();
		}
	}
	return simp;
}

///////
// SOLVE METHODS
///////

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

bool PCSolver::solve(const vec<Lit>& assumptions, Solution* sol){
	if(optim!=NONE && sol->getNbModelsToFind()!=1){
		throw idpexception("Finding multiple models can currently not be combined with optimization.\n");
	}

	if(!sol->getSearch()){
		return getSolver()->solve(assumptions, true);
	}

	bool moremodels = true;

	if(verbosity()>=1){
		reportf("> Conflicts |          ORIGINAL         |          LEARNT          | Progress\n");
		reportf(">           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |         \n");
	}

	while (moremodels && (sol->getNbModelsToFind() == 0 || sol->getNbModelsFound() < sol->getNbModelsToFind())) {
		vec<Lit> model;
		bool found = false;
		if(optim!=NONE){
			found = findOptimal(assumptions, model, sol);
			if(!found){
				moremodels = false;
			}
			if(found){
				getParent()->modelWasOptimal();
			}
		}else{
			found = findNext(assumptions, model, moremodels);
			if (found) {
				getParent()->addModel(model, sol);
			}
		}
	}

	if (verbosity()>=1) {
		clog <<"> Found " <<sol->getNbModelsFound() <<" models, ";
		if(!moremodels){
			clog <<"no more models exist.\n";
		}else if(optim==NONE){
			clog <<"searched for " <<sol->getNbModelsToFind() <<" models.\n";
		}
	}

	return sol->getNbModelsFound()>0;
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
bool PCSolver::findNext(const vec<Lit>& assmpt, vec<Lit>& m, bool& moremodels) {
	bool rslt = getSolver()->solve(assmpt);

	if (!rslt) {
		moremodels = false;
		return false;
	}

	m.clear();

	for (uint64_t i = 0; i < nVars(); i++) {
		if (value(i) == l_True) {
			m.push(mkLit(i, false));
		} else if (value(i) == l_False) {
			m.push(mkLit(i, true));
		}
	}

	//check if more models can exist
	if (getSolver()->decisionLevel() != assmpt.size()) { //choices were made, so other models possible
		vec<Lit> invalidation;
		invalidate(invalidation);
		moremodels = invalidateModel(invalidation);
	} else {
		moremodels = false; //no more models possible
	}

	return true;
}

void PCSolver::invalidate(vec<Lit>& invalidation) {
	// Add negation of model as clause for next iteration.
	// add all choice literals
	vector<Lit> v = getSolver()->getDecisions();
	for (vector<Lit>::const_iterator i = v.begin(); i < v.end(); i++) {
		invalidation.push(~(*i));
	}
	// Remove doubles.
	sort(invalidation);
	Lit p = lit_Undef;
	int i = 0, j = 0;
	for (; i < invalidation.size(); i++) {
		if (invalidation[i] != p) {
			invalidation[j++] = (p = invalidation[i]);
		}
	}
	invalidation.shrink(i - j);
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
bool PCSolver::invalidateModel(vec<Lit>& learnt) {
	//TODO: do not backtrack to 0, but do analyzefinal on learnt to check to which level to backtrack.
	//for subsetminimize this is not so clear, because assumptions have to be added too, so maybe there backtrack to 0 is necessary (for unit propagation before search)
	getSolver()->cancelUntil(0);

	if (modes().verbosity >= 3) {
		clog <<"Adding model-invalidating clause: [ ";
		Print::print(learnt);
		clog <<"]\n";
	}

	bool result = addClause(learnt);

	getSolver()->varDecayActivity();
	getSolver()->claDecayActivity();

	if (modes().verbosity >= 3) {
		clog <<"Model invalidated.\n";
	}

	return result;
}

/************************
 * OPTIMIZATION METHODS *
 ************************/

bool PCSolver::addMinimize(const vec<Lit>& lits, bool subsetmnmz) {
	if (lits.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}
	if (optim != NONE) {
		throw idpexception("At most one set of literals to be minimized can be given.\n");
	}

	if (modes().verbosity >= 3) {
		clog <<"Added minimization condition: %sinimize [" <<(subsetmnmz?"Subsetm":"M");
		bool first = true;
		for (int i = 0; i < lits.size(); i++) {
			if (!first) {
				clog <<(subsetmnmz?" ":"<");
			}
			first = false;
			clog <<lits[i];
		}
		clog <<"]\n";
	}

	if (subsetmnmz) {
		optim = SUBSETMNMZ;
	} else {
		optim = MNMZ;
	}

	addVars(lits);
	for (int i = 0; i < lits.size(); i++) {
		to_minimize.push(lits[i]);
	}

	return true;
}

bool PCSolver::addMinimize(const Var head, const int setid, AggType agg) {
	if (optim != NONE) {
		throw idpexception("Only one optimization statement is allowed.\n");
	}

	addVar(head);
	optim = AGGMNMZ;
	this->head = head;
	vec<Lit> cl;
	cl.push(mkLit(head, false));
	bool notunsat = addClause(cl);
	if (notunsat) {
		assert(getAggSolver()!=NULL);
		notunsat = getAggSolver()->addMnmz(head, setid, agg);
	}

	return notunsat;
}

bool PCSolver::invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt) {
	int subsetsize = 0;

	for (int i = 0; i < to_minimize.size(); i++) {
		if (getSolver()->model[var(to_minimize[i])] == l_True) {
			invalidation.push(~to_minimize[i]);
			subsetsize++;
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

	for (int i = 0; !currentoptimumfound && i < to_minimize.size(); i++) {
		if (!currentoptimumfound && getSolver()->model[var(to_minimize[i])] == l_True) {
			if (modes().verbosity >= 1) {
				clog <<"Current optimum found for: ";
				getParent()->printLiteral(cerr, to_minimize[i]);
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
 *
 * Returns true if an optimal model was found
 */
bool PCSolver::findOptimal(const vec<Lit>& assmpt, vec<Lit>& m, Solution* sol) {
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
			for (int i = 0; i < nvars; i++) {
				if (value(i) == l_True) {
					m.push(mkLit(i, false));
				} else if (value(i) == l_False) {
					m.push(mkLit(i, true));
				}
			}
		}
	}*/

	while (!unsatreached) {
		if (optim == AGGMNMZ) {
			assert(getAggSolver()!=NULL);
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			getAggSolver()->propagateMnmz(head);
		}

		bool sat = getSolver()->solve(currentassmpt);
		if(!sat){
			unsatreached = true;
			break;
		}
		if (sat) {
			modelfound = true;
			//Store current model in m before invalidating the solver
			m.clear();
			int nvars = (int) nVars();
			for (int i = 0; i < nvars; i++) {
				if (value(i) == l_True) {
					m.push(mkLit(i, false));
				} else if (value(i) == l_False) {
					m.push(mkLit(i, true));
				}
			}

			//invalidate the solver
			vec<Lit> invalidation;
			switch (optim) {
			case MNMZ:
				unsatreached = invalidateValue(invalidation);
				break;
			case SUBSETMNMZ:
				currentassmpt.clear();
				unsatreached = invalidateSubset(invalidation, currentassmpt);
				break;
			case AGGMNMZ:
				//FIXME the invalidation turns out to be empty
				unsatreached = getAggSolver()->invalidateAgg(invalidation, head);
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

			getParent()->addModel(m, sol);
		}
	}

	return modelfound && unsatreached;
}

///////
// PRINT METHODS
///////

void PCSolver::printModID() const {
	if(getModSolver()!=NULL){
		clog <<"mod s " <<getModSolver()->getPrintId();
	}
}

void PCSolver::printEnqueued(const Lit& p) const{
	clog <<"Enqueued " <<p <<" in ";
	printModID();
	reportf("\n");
}

void PCSolver::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		clog <<"Choice literal, dl " <<level <<", ";
		printModID();

		clog <<": " <<l <<".\n";
	}
}

void PCSolver::printStatistics() const {
	getSolver()->printStatistics();
	for(solverlist::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if((*i)->present){
			(*i)->get()->printStatistics();
		}
	}
}

void PCSolver::print() const{
	Print::print(getSolver());
	for(vector<DPLLTSolver*>::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		(*i)->get()->print();
	}
}

void PCSolver::print(rClause clause) const {
	getSolver()->printClause(getClauseRef(clause));
}
