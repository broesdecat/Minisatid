//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#include "solvers/theorysolvers/PCSolver.hpp"

#include "solvers/satsolver/SATSolver.h"
#include "solvers/external/ExternalInterface.hpp"
#include "solvers/modules/IDSolver.hpp"
#include "solvers/modules/AggSolver.hpp"
#include "solvers/modules/ModSolver.hpp"

#include "solvers/utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

/******************
 * INITIALIZATION *
 ******************/

int PCSolver::getModPrintID() const {
	if (modsolver != NULL) {
		return (int) modsolver->getPrintId();
	}
	return 0;
}

//Has to be value copy of modes!
PCSolver::PCSolver(ECNF_mode modes, MinisatID::WrappedLogicSolver* inter) :
		LogicSolver(modes, inter),
		solver(NULL), idsolver(NULL), cpsolver(NULL), aggsolver(NULL), modsolver(NULL),
		aggcreated(false), idcreated(false),
		aggsolverpresent(false), idsolverpresent(false), modsolverpresent(false),
		init(true),
		optim(NONE), head(-1){
	solver = new Solver(this);
	if (modes.disableheur) {
		solver->disableHeur();
	}

	if (modes.def) {
		idsolver = new IDSolver(this);
		idcreated = true;
	}
	idsolverpresent = idcreated;
	if (modes.aggr) {
		aggsolver = new AggSolver(this);
		aggcreated = true;
	}
	aggsolverpresent = aggcreated;
	if (modes.def && modes.aggr) {
		idsolver->setAggSolver(aggsolver);
	}

	//TODO which variables to initialize depends on sat solver!
	//solver->maxruntime = modes.maxruntime;
	//solver->polarity_mode = modes.polarity_mode;
	solver->random_var_freq = modes.random_var_freq;
	solver->verbosity = modes.verbosity;
	solver->var_decay = modes.var_decay;
}

PCSolver::~PCSolver() {
	if (idcreated) {
		delete idsolver;
	}
	if (aggcreated) {
		delete aggsolver;
	}
	delete solver;
}

inline pSolver 		PCSolver::getSolver() 		const { return solver; }
inline pIDSolver 	PCSolver::getIDSolver()		const { return idsolver; }
inline pAggSolver 	PCSolver::getAggSolver()	const { return aggsolver; }
inline pModSolver 	PCSolver::getModSolver()	const { return modsolver; }

Solver 		const * PCSolver::getCSolver() 		const { return solver; }
IDSolver 	const * PCSolver::getCIDSolver() 	const { return idsolver; }
AggSolver 	const * PCSolver::getCAggSolver() 	const { return aggsolver; }
ModSolver 	const * PCSolver::getCModSolver() 	const { return modsolver; }

void PCSolver::setModSolver(pModSolver m) {
	modsolver = m;
	modsolverpresent = true;
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

void PCSolver::setTrue(Lit p, PropBy solver, rClause c) {
	assert(solver!=BYAGG || aggsolverpresent);
	assert(solver!=BYDEF || idsolverpresent);

	propagations[var(p)] = solver;
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

uint64_t PCSolver::getConflicts() const {
	return getSolver()->conflicts;
}

void PCSolver::varBumpActivity(Var v) {
	if (!modes().disableheur) {
		getSolver()->varBumpActivity(v);
	}
}

/************************
 * EXTENDING THE THEORY *
 ************************/

Var PCSolver::newVar() {
	assert(!init);
	Var v = nVars();
	addVar(v);
	return v;
}

void PCSolver::addVar(Var v) {
	assert(v>-1);
	while (v >= nVars()) {
		getSolver()->newVar(true, false);
		if (idsolverpresent) {
			getIDSolver()->notifyVarAdded(nVars());
		}
		if (aggsolverpresent) {
			getAggSolver()->notifyVarAdded(nVars());
		}
	}
	getSolver()->setDecisionVar(v, true); // S.nVars()-1   or   var
	if (!init) {
		propagations.resize(nVars(), NOPROP);
	}
}

void PCSolver::addVars(const vec<Lit>& a) {
	for (int i = 0; i < a.size(); i++) {
		addVar(var(a[i]));
	}
}

bool PCSolver::addClause(vec<Lit>& lits) {
	if (modes().verbosity >= 7) {
		report("Adding clause:");
		for (int i = 0; i < lits.size(); i++) {
			report(" ");
			gprintLit(lits[i]);
		}
		report("\n");
	}
	addVars(lits);
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
	assert(idsolverpresent);
	addVar(head);
	addVars(lits);
	return getIDSolver()->addRule(conj, head, lits);
}

bool PCSolver::addSet(int setid, const vec<Lit>& lits) {
	assert(aggsolverpresent);
	addVars(lits);
	vector<Weight> w;
	w.resize(lits.size(), 1);
	return addSet(setid, lits, w);
}

bool PCSolver::addSet(int setid, const vec<Lit>& lits, const vector<Weight>& w) {
	assert(aggsolverpresent);
	addVars(lits);
	vector<Lit> ll;
	for (int i = 0; i < lits.size(); i++) {
		ll.push_back(lits[i]);
	}
	return getAggSolver()->addSet(setid, ll, w);
}

bool PCSolver::addAggrExpr(Lit head, int setid, Weight bound, AggSign boundsign, AggType type, AggSem defined) {
	assert(aggsolverpresent);

	if (modes().verbosity >= 7) {
		report("Adding aggregate with info ");
		gprintLit(head);
		report(", %d, %d, %s, %d, %s \n", setid, bound, boundsign==LB?"lower":"greater", type, defined==DEF?"defined":"completion");
	}

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
bool PCSolver::finishParsing() {
	init = false;

	//Datastructures that are not necessary beforehand, are much cheaper to only initialize once!
	propagations.resize(nVars(), NOPROP);

	//important to call definition solver last
	if (aggsolverpresent) {
		bool unsat;
		getAggSolver()->finishParsing(aggsolverpresent, unsat);
		if (unsat) {
			return false;
		}
	}
	if (idsolverpresent) {
		bool idpropagations = getIDSolver()->finishECNF_DataStructures();
		if (idpropagations) {
			//FIXME test this:
			//idsolverpresent = getIDSolver()->finishECNF_DataStructures(); //Here idsolver is deleted if no recursive pos or neg loops are possible
			//if (idsolverpresent) {
			if (!getIDSolver()->initAfterSimplify()) {
				return false;
			}
		} else {
			//idsolverpresent = false;
			if (modes().verbosity > 0) {
				report("|    (there will be no definitional propagations)                             |\n");
			}
		}
	}

	// Do all propagations that have already been done on the SAT-solver level.
	for (vector<Lit>::const_iterator i = initialprops.begin(); i < initialprops.end(); i++) {
		if (propagate(*i) != nullPtrClause) {
			return false;
		}
	}
	initialprops.clear();
	if (propagateAtEndOfQueue() != nullPtrClause) {
		return false;
	}

	if (!aggsolverpresent) {
		if (modes().verbosity > 0) {
			report("|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
		}
	}

	//TODO later modes.mnmz, modes.cp

	// TODO Pre processing
	/*if(aggsolverpresent){
	 getAggSolver()->findClausalPropagations();
	 }*/

	return true;
}

/*********************
 * IDSOLVER SPECIFIC *
 *********************/

void PCSolver::removeAggrHead(Var x) {
	if (idsolverpresent) {
		getIDSolver()->removeAggrHead(x);
	}
}

void PCSolver::notifyAggrHead(Var x) {
	if (idsolverpresent) {
		getIDSolver()->notifyAggrHead(x);
	}
}

//if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status
lbool PCSolver::checkStatus(lbool status) const {
	if (!idsolverpresent || status != l_True) {
		return status;
	}

	if (modes().sem == WELLF && !getIDSolver()->isWellFoundedModel()) {
		return l_False;
	}
	return status;
}

/**********************
 * AGGSOLVER SPECIFIC *
 **********************/

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(Lit l) {
	if (modes().verbosity > 2) {
		report("Find T-theory explanation for ");
		gprintLit(l);
		report("\n");
	}

	PropBy solver = propagations[var(l)];
	assert(solver!=BYSAT && solver!=NOPROP);

	rClause explan = nullPtrClause;

	switch (solver) {
	case BYAGG:
		explan = getAggSolver()->getExplanation(l);
		break;
	case BYDEF:
		explan = getIDSolver()->getExplanation(l);
		break;
	default:
		assert(false);
	}

	if (verbosity() >= 2) {
		report("Implicit %s reason clause for ", solver==BYAGG?"aggregate":"definitional");
		gprintLit(l, sign(l) ? l_False : l_True);
		report(" : ");
		Print::printClause(explan, this);
		report("\n");
	}

	assert(explan!=nullPtrClause);

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

/////
// SAT SOLVER SPECIFIC
///////

void PCSolver::backtrackRest(Lit l) {
	if (aggsolverpresent) {
		getAggSolver()->backtrack(l);
	}
	if (idsolverpresent) {
		getIDSolver()->backtrack(l);
	}
	if (modsolverpresent) {
		getModSolver()->backtrackFromSameLevel(l);
	}
}

// Called by SAT solver when new decision level is started, BEFORE choice has been made!
void PCSolver::newDecisionLevel() {
	if (idsolverpresent) {
		getIDSolver()->newDecisionLevel();
	}
	if (aggsolverpresent) {
		getAggSolver()->newDecisionLevel();
	}
}

//TODO implementeer ze hier allemaal
void PCSolver::backtrackDecisionLevel(int levels) {
	for (int i = 0; i < levels; i++) {
		if (aggsolverpresent) {
			getAggSolver()->backtrackDecisionLevel();
		}
	}
}

/**
 * Returns not-owning pointer
 */
//TODO: maybe let all lower ones return owning pointer, so only one reference to addlearnedclause?
rClause PCSolver::propagate(Lit l) {
	if (init) {
		initialprops.push_back(l);
		return nullPtrClause;
	}

	rClause confl = nullPtrClause;
	if (aggsolverpresent) {
		confl = getAggSolver()->propagate(l);
	}
	if (idsolverpresent && confl == nullPtrClause) {
		confl = getIDSolver()->propagate(l);
	}
	if (modsolverpresent && confl == nullPtrClause) {
		confl = getModSolver()->propagate(l);
	}
	return confl;
}

/**
 * Returns not-owning pointer
 */
rClause PCSolver::propagateAtEndOfQueue() {
	rClause confl = nullPtrClause;
	if (idsolverpresent && confl == nullPtrClause) {
		confl = getIDSolver()->propagateDefinitions();
	}
	if (modsolverpresent && confl == nullPtrClause) {
		confl = getModSolver()->propagateAtEndOfQueue();
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
	if (simp && idsolverpresent) {
		simp = getIDSolver()->initAfterSimplify();
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
	if(!sol->getSearch()){
		return getSolver()->solve(assumptions, true);
	}

	if (modes().verbosity >= 1) {
		report("============================[ Search Statistics ]==============================\n");
		report("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
		report("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
		report("===============================================================================\n");
	}

	bool moremodels = true;

	while (moremodels && (sol->getNbModelsToFind() == 0 || sol->getNbModelsFound() < sol->getNbModelsToFind())) {
		vec<Lit> model;
		bool found = false;
		if(optim!=NONE){
			found = findOptimal(assumptions, model);
		}else{
			found = findNext(assumptions, model, moremodels);
		}

		if (found) {
			getParent()->addModel(model, sol);
		}
	}

	if (verbosity()>=1) {
		if(sol->getNbModelsFound() != 0 && !moremodels && sol->getNbModelsToFind() != 1){
			report("| There are no more models                                                    |\n");
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
		report("Adding model-invalidating clause: [ ");
		gprintClause(learnt);
		report("]\n");
	}

	bool result = addClause(learnt);

	getSolver()->varDecayActivity();
	getSolver()->claDecayActivity();

	if (modes().verbosity >= 3) {
		report("Model invalidated.\n");
	}

	return result;
}

/************************
 * OPTIMIZATION METHODS *
 ************************/

bool PCSolver::addMinimize(const vec<Lit>& lits, bool subsetmnmz) {
	if (!modes().mnmz) {
		throw idpexception("ERROR! Attempt at adding an optimization statement, though header "
			"did not contain \"mnmz\".\n");
	}
	if (lits.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}
	if (optim != NONE) {
		throw idpexception("At most one set of literals to be minimized can be given.\n");
	}

	if (modes().verbosity >= 3) {
		report("Added minimization condition: %sinimize [", subsetmnmz?"Subsetm":"M");
		bool first = true;
		for (int i = 0; i < lits.size(); i++) {
			if (!first) {
				report("%s", subsetmnmz?" ":"<");
			}
			first = false;
			gprintLit(lits[i]);
		}
		report("]\n");
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

bool PCSolver::addSumMinimize(const Var head, const int setid) {
	if (!modes().mnmz) {
		throw idpexception("ERROR! Attempt at adding an optimization statement, though header "
			"did not contain \"mnmz\".\n");
	}
	if (optim != NONE) {
		throw idpexception("Only one optimization statement is allowed.\n");
	}

	addVar(head);
	optim = SUMMNMZ;
	this->head = head;
	vec<Lit> cl;
	cl.push(mkLit(head, false));
	bool notunsat = addClause(cl);
	if (notunsat) {
		assert(aggsolverpresent);
		notunsat = getAggSolver()->addMnmzSum(head, setid, LB);
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
				report("Current optimum is var %d\n", gprintVar(var(to_minimize[i])));
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
 * FIXME: add code that allows to reset the solver when the optimal value has been found, to search for more models with the same optimal value.
 *
 * Returns true if an optimal model was found
 */
bool PCSolver::findOptimal(const vec<Lit>& assmpt, vec<Lit>& m) {
	vec<Lit> currentassmpt;
	assmpt.copyTo(currentassmpt);

	bool rslt = true, optimumreached = false;

	//CHECKS whether first element yields a solution, otherwise previous strategy is done
	//TODO should become dichotomic search: check half and go to interval containing solution!
	/*if(optim==MNMZ){
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

	while (!optimumreached && rslt) {
		if (optim == SUMMNMZ) {
			assert(aggsolverpresent);
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			getAggSolver()->propagateMnmz(head);
		}

		rslt = getSolver()->solve(currentassmpt);

		if (rslt && !optimumreached) {
			m.clear();
			int nvars = (int) nVars();
			for (int i = 0; i < nvars; i++) {
				if (value(i) == l_True) {
					m.push(mkLit(i, false));
				} else if (value(i) == l_False) {
					m.push(mkLit(i, true));
				}
			}

			vec<Lit> invalidation;
			switch (optim) {
			case MNMZ:
				optimumreached = invalidateValue(invalidation);
				break;
			case SUBSETMNMZ:
				currentassmpt.clear();
				optimumreached = invalidateSubset(invalidation, currentassmpt);
				break;
			case SUMMNMZ:
				//FIXME the invalidation turns out to be empty
				optimumreached = getAggSolver()->invalidateSum(invalidation, head);
				break;
			case NONE:
				assert(false);
				break;
			}

			if (!optimumreached) {
				if (getSolver()->decisionLevel() != currentassmpt.size()) { //choices were made, so other models possible
					optimumreached = !invalidateModel(invalidation);
				} else {
					optimumreached = true;
				}
			}

			if (modes().verbosity > 1) {
				printf("Temporary model: \n");
				for (int i = 0; i < m.size(); i++) {
					printf("%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "" : "-", gprintVar(var(m[i])));
				}
				printf(" 0\n");
			}

		} else if (!rslt) {
			optimumreached = true;
		}
	}

	//TODO move to upper layer to allow translation to correct format
	/*
	 if(!hasmodels){
	 assert(!optimumreached);
	 fprintf(res==NULL?stdout:res, " UNSAT\n");
	 printf("UNSATISFIABLE\n");
	 }else{
	 assert(optimumreached);
	 fprintf(res==NULL?stdout:res, " SAT\n");
	 printf("SATISFIABLE\n");
	 int nvars = (int)nVars();
	 for (int i = 0; i < nvars; i++){
	 fprintf(res==NULL?stdout:res, "%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "" : "-", i + 1);
	 }
	 fprintf(res==NULL?stdout:res, " 0\n");

	 modelsfound++;
	 }*/

	return optimumreached;
}

vector<rClause> PCSolver::getClausesWhichOnlyContain(const vector<Var>& vars) {
	return vector<rClause> ();
	//return getSolver()->getClausesWhichOnlyContain(vars);
}

///////
// PRINT METHODS
///////

void PCSolver::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		report("Choice literal, dl %d, ", level);
		if (modsolverpresent) {
			report("mod s %zu", modsolver->getPrintId());
		}
		report(": ");
		gprintLit(l);
		report(".\n");
	}
}

void PCSolver::printStatistics() const {
	getSolver()->printStatistics();
	if (idsolverpresent) {
		getIDSolver()->printStatistics();
	}
	if (aggsolverpresent) {
		getAggSolver()->printStatistics();
	}
}
