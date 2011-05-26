/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "theorysolvers/PropagatorFactory.hpp"

#include "theorysolvers/PCSolver.hpp"

#include <iostream>

#include "wrapper/InterfaceImpl.hpp"

#include "satsolver/SATSolver.hpp"
#include "modules/IDSolver.hpp"
#include "modules/AggSolver.hpp"
#include "modules/ModSolver.hpp"

#ifdef CPSUPPORT
#include "modules/CPSolver.hpp"
#endif

#include "utils/Print.hpp"
#include "utils/ECNFPrinter.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

WrappedPropagator::~WrappedPropagator(){
	if(createdhere){
		delete module;
	}
}

bool PropagatorFactory::headerunprinted = true;

//Has to be value copy of modes!
PropagatorFactory::PropagatorFactory(SolverOption modes, MinisatID::WrapperPimpl& inter) :
		LogicSolver(modes, inter),
		satsolver(NULL),
		state(THEORY_PARSING),
		nbskipped(0),
		optim(NONE), head(-1),
		state_savedlevel(0), state_savingclauses(false),
		aggsolver(NULL), modsolver(NULL),cpsolver(NULL),
		logger(new PCLogger()), ecnfprinter(NULL),
		hasMonitor(false){
	satsolver = createSolver(*this);

	if(modes.printcnfgraph){
		//FIXME
		//ecnfgraphprinter = new ECNFPrinter();
	}

	if(modes.verbosity>1){
		ecnfprinter = new ECNFPrinter();
	}

	if(hasECNFPrinter()){
		getECNFPrinter().startPrinting();
	}
}

PropagatorFactory::~PropagatorFactory() {
	deleteList<WrappedPropagator>(solvers);
	delete satsolver;
	delete logger;
	delete ecnfprinter;
}

void PropagatorFactory::setModSolver(ModSolver* m) {
	assert(isParsing());
	modsolver = new WrappedPropagator(m, false);
	solvers.insert(solvers.begin(), modsolver);
}

bool PropagatorFactory::hasIDSolver(defID id) const { return idsolvers.find(id)!=idsolvers.end(); }
bool PropagatorFactory::hasAggSolver() const { return aggsolver!=NULL; }
bool PropagatorFactory::hasModSolver() const { return modsolver!=NULL; }

bool PropagatorFactory::hasPresentIDSolver(defID id) const { return hasIDSolver(id) && idsolvers.at(id)->present; }
bool PropagatorFactory::hasPresentAggSolver() const { return hasAggSolver() && aggsolver->present; }
bool PropagatorFactory::hasPresentModSolver() const { return hasModSolver() && modsolver->present; }

void PropagatorFactory::addIDSolver(defID id){
	assert(isParsing());
	IDSolver* idsolver = new IDSolver(this);
	idsolver->notifyVarAdded(nVars());

	WrappedPropagator* dplltsolver = new WrappedPropagator(idsolver, true);
	idsolvers.insert(pair<defID, WrappedPropagator*>(id, dplltsolver));
	solvers.push_back(dplltsolver);
}

void PropagatorFactory::addAggSolver(){
	assert(isParsing());
	AggSolver* tempagg = new AggSolver(this);
	tempagg->notifyVarAdded(nVars());

	aggsolver = new WrappedPropagator(tempagg, true);
	solvers.insert(solvers.begin(), aggsolver);
}

IDSolver* PropagatorFactory::getIDSolver(defID id) const {
	assert(hasPresentIDSolver(id));
	return dynamic_cast<IDSolver*>(idsolvers.at(id)->get());
}
AggSolver* PropagatorFactory::getAggSolver() const {
	assert(hasPresentAggSolver());
	return dynamic_cast<AggSolver*>(aggsolver->get());
}
ModSolver* PropagatorFactory::getModSolver() const {
	assert(hasPresentModSolver());
	return dynamic_cast<ModSolver*>(modsolver->get());
}

lbool PropagatorFactory::value(Var x)	const { return getSolver()->value(x); }
lbool PropagatorFactory::value(Lit p)	const { return getSolver()->value(p); }
uint64_t PropagatorFactory::nVars()		const { return getSolver()->nbVars(); }

rClause PropagatorFactory::createClause(const vec<Lit>& lits, bool learned) {
	return getSolver()->makeClause(lits, learned);
}

// INITIALIZING THE THEORY

//IMPORTANT: calling this from inside is not allowed during parsing: it breaks the theory that's being read!
Var PropagatorFactory::newVar() {
	assert(isInitialized());
	Var v = nVars();
	add(v);
	return v;
}

//NOTE: if solvers are added during parsing, make sure they have up-to-date datastructures
bool PropagatorFactory::add(Var v) {
	assert(v>-1);

	while (((uint64_t) v) >= nVars()) {
#ifdef USEMINISAT22
		getSolver()->newVar(modes().polarity==POL_TRUE?l_True:modes().polarity==POL_FALSE?l_False:l_Undef, false);
#else
		getSolver()->newVar(true, false);
#endif
		for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
			if((*i)->present){
				(*i)->get()->notifyVarAdded(nVars());
			}
		}
	}

	getSolver()->setDecisionVar(v, true);
	logger->addCount(v);

	if (isInitialized()) { //Lazy init
		propagations.resize(nVars(), NULL);
	}
	return true;
}

void PropagatorFactory::addVars(const vec<Lit>& a) {
	for (int i = 0; i < a.size(); ++i) {
		add(var(a[i]));
	}
}

void PropagatorFactory::addVars(const vector<Lit>& a) {
	for (vector<Lit>::const_iterator i=a.begin(); i < a.end(); ++i) {
		add(var(*i));
	}
}

//FIXME add potential modal ID to the ECNF printer!

bool PropagatorFactory::add(const InnerDisjunction& disj){
	addVars(disj.literals);

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(disj);
	}

	return getSolver()->addClause(disj.literals);
}

bool PropagatorFactory::add(const InnerEquivalence& eq){
	addVar(eq.head);
	addVars(eq.literals);
	bool notunsat = true;

	//create the completion
	vec<Lit> comp;
	comp.push(eq.head);

	for (int i = 0; i < eq.literals.size(); ++i) {
		comp.push(eq.literals[i]);
	}

	if (eq.conjunctive) {
		for (int i = 1; i < comp.size(); ++i) {
			comp[i] = ~comp[i];
		}
	} else {
		comp[0] = ~comp[0];
	}

	InnerDisjunction clause;
	comp.copyTo(clause.literals);
	notunsat = add(clause);

	for (int i = 1; notunsat && i < comp.size(); ++i) {
		InnerDisjunction binclause;
		binclause.literals.push(~comp[0]);
		binclause.literals.push(~comp[i]);
		notunsat = add(binclause);
	}

	return notunsat;
}
bool PropagatorFactory::add(const InnerRule& rule){
	if(!hasIDSolver(rule.definitionID)){
		addIDSolver(rule.definitionID);
	}
	assert(hasPresentIDSolver(rule.definitionID));

	add(rule.head);
	addVars(rule.body);

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(rule);
	}

	return getIDSolver(rule.definitionID)->addRule(rule.conjunctive, mkLit(rule.head, false), rule.body);
}
bool PropagatorFactory::add(const InnerWSet& wset){
	if(!hasAggSolver()){
		addAggSolver();
	}
	assert(hasPresentAggSolver());

	addVars(wset.literals);

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(wset);
	}

	return getAggSolver()->addSet(wset.setID, wset.literals, wset.weights);
}
bool PropagatorFactory::add(const InnerAggregate& agg){
	if(!hasPresentAggSolver()){
		stringstream ss;
		ss <<"The set with id " <<agg.setID <<" should be defined before the aggregate with head " <<agg.head <<"\n";
		throw idpexception(ss.str());
	}
	add(agg.head);

	// IMPORTANT: create the definition solver as soon as possible (impossible to create it when parsing is finished)
	if(!hasIDSolver(agg.defID)){
		addIDSolver(agg.defID);
	}

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(agg);
	}

	return getAggSolver()->addAggrExpr(agg.head, agg.setID, agg.bound, agg.sign, agg.type, agg.sem, agg.defID);
}
bool PropagatorFactory::add(const InnerMinimizeSubset& mnm){
	if (mnm.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}
	if (optim != NONE) {
		throw idpexception("At most one set of literals to be minimized can be given.\n");
	}

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(mnm);
	}

	optim = SUBSETMNMZ;

	addVars(mnm.literals);
	for (int i = 0; i < mnm.literals.size(); ++i) {
		to_minimize.push(mnm.literals[i]);
	}

	return true;
}

bool PropagatorFactory::add(const InnerMinimizeOrderedList& mnm){
	if (mnm.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}
	if (optim != NONE) {
		throw idpexception("At most one set of literals to be minimized can be given.\n");
	}

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(mnm);
	}

	optim = MNMZ;

	addVars(mnm.literals);
	for (int i = 0; i < mnm.literals.size(); ++i) {
		to_minimize.push(mnm.literals[i]);
	}

	return true;
}
bool PropagatorFactory::add(const InnerMinimizeAgg& mnm){
	if (optim != NONE) {
		throw idpexception(">> Only one optimization statement is allowed.\n");
	}

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(mnm);
	}

	add(mnm.head);
	optim = AGGMNMZ;
	this->head = mnm.head;
	InnerDisjunction clause;
	clause.literals.push(mkLit(mnm.head, false));
	bool notunsat = add(clause);
	if (notunsat) {
		assert(getAggSolver()!=NULL);
		notunsat = getAggSolver()->addMnmz(mnm.head, mnm.setID, mnm.type);
	}

	return notunsat;
}
bool PropagatorFactory::add(const InnerForcedChoices& choices){
	if (choices.forcedchoices.size() != 0) {
		getSolver()->addForcedChoices(choices.forcedchoices);
	}
	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(choices);
	}
	return true;
}

bool PropagatorFactory::add(const InnerSymmetryLiterals& symms){
	getSolver()->addSymmetryGroup(symms.literalgroups);
	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(symms);
	}
	return true;
}

bool PropagatorFactory::hasCPSolver() const { return cpsolver!=NULL; }
bool PropagatorFactory::hasPresentCPSolver() const { return hasCPSolver() && cpsolver->present; }

template<class T>
bool PropagatorFactory::addCP(const T& formula){
#ifndef CPSUPPORT
	assert(false);
	exit(1);
#else
	if(!hasCPSolver()){
		addCPSolver();
	}
	assert(hasPresentCPSolver());
	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(formula);
	}
	return getCPSolver()->add(formula);
#endif
}

#ifdef CPSUPPORT
#warning Counting models in the presence of CP variables will be an underapproximation! (finding only one variable assigment for each literal assignment)
void PropagatorFactory::addCPSolver(){
	assert(isParsing());
	CPSolver* temp = new CPSolver(this);
	temp->notifyVarAdded(nVars());

	cpsolver = new WrappedPropagator(temp, true);
	solvers.insert(solvers.begin(), cpsolver);
}

CPSolver* PropagatorFactory::getCPSolver() const {
	assert(hasPresentCPSolver());
	return dynamic_cast<CPSolver*>(cpsolver->get());
}
#endif

bool PropagatorFactory::add(const InnerIntVarRange& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerIntVarEnum& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPBinaryRel& obj){
	add(obj.head);
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPBinaryRelVar& obj){
	add(obj.head);
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPSumWeighted& obj){
	add(obj.head);
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPCount& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPAllDiff& obj){
	return addCP(obj);
}


/*
 * Returns "false" if UNSAT was already found, otherwise "true"
 *
 * IMPORTANT: before finishparsing, derived propagations are not propagated to the solvers, so after their finishparsing, we redo
 * all those propagations for the solvers
 */
void PropagatorFactory::finishParsing(bool& unsat) {
	assert(isParsing());
	state = THEORY_INITIALIZING;
	unsat = false;

	propagations.resize(nVars(), NULL); //Lazy init

	//Notify parsing is over
	for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		if((*i)->present){
			(*i)->get()->notifyParsed();
		}
	}

	//Finish all solvers
	//NOTE Both aggsolver and modsolver can add rules during their initialization, so always initialize all ID solver last!
	for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		if((*i)->present){
			(*i)->get()->finishParsing((*i)->present, unsat);
			(*i)->get()->notifyInitialized();
			if(unsat){
				return;
			}
		}
	}

	for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		if ((*i)->present && !(*i)->get()->simplify()) {
			unsat = true; return;
		} else if(!(*i)->present) {
			if (modes().verbosity > 0) {
				clog <<">    (there will be no propagations on " <<(*i)->get()->getName() <<" module)\n";
			}
		}
	}

	// Do all propagations that have already been done on the SAT-solver level.
	state = THEORY_INITIALIZED;
	for (vector<Lit>::const_iterator i=initialprops.begin(); i < initialprops.end(); ++i) {
		if (propagate(*i) != nullPtrClause) {
			unsat = true; return;
		}
	}

	if (propagateAtEndOfQueue() != nullPtrClause) {
		unsat = true; return;
	}

	if(modes().useaggheur){
		getSATSolver()->notifyCustomHeur();
	}

	// Aggregate pre processing idea
	/*if(aggsolverpresent){
	 getAggSolver()->findClausalPropagations();
	 }*/

	if(hasECNFPrinter()){
		getECNFPrinter().endPrinting(clog);
	}
}

// IDSOLVER SPECIFIC

void PropagatorFactory::removeAggrHead(Var head, int defID) {
	if (hasPresentIDSolver(defID)) {
		getIDSolver(defID)->removeAggrHead(head);
	}
}

void PropagatorFactory::notifyAggrHead(Var x, int defID) {
	if (hasPresentIDSolver(defID)) {
		getIDSolver(defID)->notifyAggrHead(x);
	}
}

/**
 * Returns OWNING pointer (faster).
 */
rClause PropagatorFactory::getExplanation(Lit l) {
	if (modes().verbosity > 2) {
		clog <<"Find T-theory explanation for " <<l <<"\n";
	}

	Propagator* solver = propagations[var(l)];
	assert(solver!=NULL); //If this happens, there is usually an error in the generated explanations!

	rClause explan = solver->getExplanation(l);
	assert(explan!=nullPtrClause);

	if (verbosity() >= 2) {
		clog <<"Implicit reason clause from the " <<solver->getName() <<" module ";
		MinisatID::print(l, sign(l) ? l_False : l_True);
		clog <<" : ";
		MinisatID::print(explan, *this);
		clog <<"\n";
	}

	return explan;
}

/*
 * @pre: p has been assigned in the current decision level!
 * Returns true if l was asserted before p
 */
bool PropagatorFactory::assertedBefore(const Var& l, const Var& p) const {
	//Check if level is lower
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
void PropagatorFactory::newDecisionLevel() {
	for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		if((*i)->present){
			(*i)->get()->newDecisionLevel();
		}
	}
}

void PropagatorFactory::backtrackDecisionLevel(int levels, int untillevel) {
	if(isBeingMonitored()){
		InnerBacktrack backtrack;
		backtrack.untillevel = untillevel;
		notifyMonitor(backtrack);
	}

	for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		if((*i)->present){
			(*i)->get()->backtrackDecisionLevels(levels, untillevel);
		}
	}
}

/**
 * Returns not-owning pointer
 */
rClause PropagatorFactory::propagate(Lit l) {
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

	rClause confl = nullPtrClause;
	for(solverlist::const_iterator i=getSolvers().begin(); confl==nullPtrClause && i<getSolvers().end(); ++i){
		if((*i)->present){
			confl = (*i)->get()->propagate(l);
		}
	}

	return confl;
}

/**
 * Returns not-owning pointer
 */
rClause PropagatorFactory::propagateAtEndOfQueue() {
	if(!isInitialized()){ return nullPtrClause;	}

	rClause confl = nullPtrClause;
	for(solverlist::const_iterator i=getSolvers().begin(); confl==nullPtrClause && i<getSolvers().end(); ++i){
		if((*i)->present){

			int sizebefore = getSolver()->getTrail().size();

			confl = (*i)->get()->propagateAtEndOfQueue();

			int sizeafter = getSolver()->getTrail().size();
			//NOTE! if any solver has made any propagation, we go back to unit propagation first!
			if(sizebefore<sizeafter){
				return confl;
			}
		}
	}
	return confl;
}

// NOTE the sat solver calls this simplify, not his own!
bool PropagatorFactory::simplify() {
	bool simp = getSolver()->simplify();
	for(solverlist::const_iterator i=getSolvers().begin(); simp && i<getSolvers().end(); ++i){
		if((*i)->present){
			simp = (*i)->get()->simplify();
		}
	}
	return simp;
}

Var PropagatorFactory::changeBranchChoice(const Var& chosenvar){
	Var newvar = chosenvar;
	if(hasAggSolver()){
		newvar = getAggSolver()->changeBranchChoice(chosenvar);
	}
	return newvar;
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
bool PropagatorFactory::solve(const vec<Lit>& assumptions, const ModelExpandOptions& options){
	if(optim!=NONE && options.nbmodelstofind!=1){
		throw idpexception("Finding multiple models can currently not be combined with optimization.\n");
	}

	if(options.search==PROPAGATE){ //Only do unit propagation
		return getSolver()->solve(assumptions, true);
	}

	if(verbosity()>=1){
		clog <<">>> Search start\n";
		if(headerunprinted){
			clog <<"> Conflicts |          ORIGINAL         |          LEARNT          | Progress\n";
			clog <<">           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |         \n";
			headerunprinted = false;
		}
	}

	if(optim!=NONE){
		findOptimal(assumptions, options);
	}else{
		bool moremodels = findNext(assumptions, options);
		if(!moremodels){
			//FIXME do not print UNSAT when not printing models
			if(getParent().getNbModelsFound() == 0){
				printNoModels(clog, verbosity());
			}else{
				printNoMoreModels(clog, verbosity());
			}
		}
	}

	if(verbosity()>=1){
		clog <<">>> Search done\n";
	}

	return getParent().getNbModelsFound()>0;
}

void PropagatorFactory::extractLitModel(InnerModel* fullmodel){
	fullmodel->litassignments.clear();

	for (uint64_t i = 0; i < nVars(); ++i) {
		if (value(i) == l_True) {
			fullmodel->litassignments.push(mkLit(i, false));
		} else if (value(i) == l_False) {
			fullmodel->litassignments.push(mkLit(i, true));
		}
	}
}

void PropagatorFactory::extractVarModel(InnerModel* fullmodel){
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
bool PropagatorFactory::findNext(const vec<Lit>& assmpt, const ModelExpandOptions& options) {
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

void PropagatorFactory::invalidate(InnerDisjunction& clause) {
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
bool PropagatorFactory::invalidateModel(InnerDisjunction& clause) {
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

bool PropagatorFactory::invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt) {
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

bool PropagatorFactory::invalidateValue(vec<Lit>& invalidation) {
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
bool PropagatorFactory::findOptimal(const vec<Lit>& assmpt, const ModelExpandOptions& options) {
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

// MOD SOLVER

bool PropagatorFactory::add(InnerDisjunction& disj, rClause& newclause){
	addVars(disj.literals);

	if(hasECNFPrinter()){
		getECNFPrinter().notifyadded(disj);
	}

	return getSolver()->addClause(disj.literals, newclause);
}

void PropagatorFactory::saveState(){
	state_savedlevel = getCurrentDecisionLevel();
	state_savingclauses = true;
}

void PropagatorFactory::resetState(){
	backtrackTo(state_savedlevel);
	assert(state_savedlevel == getCurrentDecisionLevel());
	state_savingclauses = false;
#warning RESET STATE INCORRECT
	//getSolver()->removeClauses(state_savedclauses);
	state_savedclauses.clear();
	//getSolver()->removeAllLearnedClauses();

}

// PRINT METHODS

string PropagatorFactory::getModID() const {
	stringstream ss;
	if(hasModSolver()){
		ss <<getModSolver()->getPrintId();
	}
	return ss.str();
}

void PropagatorFactory::printEnqueued(const Lit& p) const{
	clog <<"> Enqueued " <<p;
	if(hasModSolver()){
		clog <<" in modal solver " <<getModID();
	}
	reportf("\n");
}

void PropagatorFactory::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		clog <<"> Choice literal, dl " <<level <<", ";
		if(hasModSolver()){
			clog <<" in modal solver " <<getModID();
		}

		clog <<": " <<l <<".\n";
	}
}

void PropagatorFactory::printStatistics() const {
	getSolver()->printStatistics();
	for(solverlist::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		if((*i)->present){
			(*i)->get()->printStatistics();
		}
	}
}

void PropagatorFactory::printState() const{
	MinisatID::print(getSolver());
	for(vector<WrappedPropagator*>::const_iterator i=getSolvers().begin(); i<getSolvers().end(); ++i){
		(*i)->get()->printState();
	}
}

void PropagatorFactory::printClause(rClause clause) const {
	getSolver()->printClause(getClauseRef(clause));
}

void PropagatorFactory::printCurrentOptimum(const Weight& value) const{
	getParent().printCurrentOptimum(value);
}
