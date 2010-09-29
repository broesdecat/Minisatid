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

#include "solvers/pcsolver/PCSolver.hpp"

#include "solvers/SATSolver.h"
#include "solvers/idsolver/IDSolver.hpp"
#include "solvers/aggsolver/AggSolver.hpp"
#include "solvers/modsolver/ModSolver.hpp"

#include "solvers/utils/Print.hpp"

bool isPositive(Lit l) {
	return !sign(l);
}
Lit createNegativeLiteral(Var i) {
	return mkLit(i, true);
}
Lit createPositiveLiteral(Var i) {
	return mkLit(i, false);
}

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
PCSolver::PCSolver(ECNF_mode modes) :
	Data(modes), solver(NULL), idsolver(NULL), aggsolver(NULL),
			modsolver(NULL), cpsolver(NULL), aggcreated(false),
			idcreated(false), aggsolverpresent(false),
			idsolverpresent(false), modsolverpresent(false),
			nb_models(modes.nbmodels), modelsfound(0), optim(NONE), head(-1), init(true),
			decisionlevels(0){
	solver = new Solver(this);
	if(modes.disableheur){
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

	//TODO depends on sat solver!
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

void PCSolver::setNbModels(int nb) {
	nb_models = nb;
}

inline pSolver PCSolver::getSolver() const {
	return solver;
}

inline pIDSolver PCSolver::getIDSolver() const {
	return idsolver;
}

inline pAggSolver PCSolver::getAggSolver() const {
	return aggsolver;
}

inline pModSolver PCSolver::getModSolver() const {
	return modsolver;
}

Solver const * PCSolver::getCSolver() const {
	return solver;
}

IDSolver const * PCSolver::getCIDSolver() const {
	return idsolver;
}

AggSolver const * PCSolver::getCAggSolver() const {
	return aggsolver;
}

ModSolver const * PCSolver::getCModSolver() const {
	return modsolver;
}

void PCSolver::setModSolver(pModSolver m) {
	modsolver = m;
	modsolverpresent = true;
}

lbool PCSolver::value(Var x) const {
	return getSolver()->value(x);
}

lbool PCSolver::value(Lit p) const {
	return getSolver()->value(p);
}

uint64_t PCSolver::nVars() const {
	return getSolver()->nbVars();
}

rClause PCSolver::createClause(vec<Lit>& lits, bool learned){
	return getSolver()->makeClause(lits, learned);
}

void PCSolver::addLearnedClause(rClause c) {
	getSolver()->addLearnedClause(c);
}

void PCSolver::backtrackTo(int level) {
	getSolver()->cancelUntil(level);
}

void PCSolver::setTrue(Lit p, rClause c) {
	getSolver()->uncheckedEnqueue(p, c);
}

int PCSolver::getLevel(int var) const {
	return getSolver()->getLevel(var);
}

vector<Lit> PCSolver::getRecentAssignments() const {
	return getSolver()->getRecentAssignments();
}

int PCSolver::getNbDecisions() const {
	return getSolver()->decisionLevel();
}

vector<Lit> PCSolver::getTrail() const {
	return getSolver()->getTrail();
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
	if(!modes().disableheur){
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
}

void PCSolver::addVars(const vec<Lit>& a) {
	for (int i = 0; i < a.size(); i++) {
		//reportf("Adding var %d\n", var(a[i]));
		addVar(var(a[i]));
	}
}

bool PCSolver::addClause(vec<Lit>& lits) {
	if (modes().verbosity >= 7) {
		reportf("Adding clause:");
		for (int i = 0; i < lits.size(); i++) {
			reportf(" ");
			gprintLit(lits[i]);
		}
		reportf("\n");
	}
	addVars(lits);
	return getSolver()->addClause(lits);
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
	for(int i=0; i<lits.size(); i++){
		ll.push_back(lits[i]);
	}
	return getAggSolver()->addSet(setid, ll, w);
}

bool PCSolver::addAggrExpr(Lit head, int setid, Weight bound, AggSign boundsign, AggType type, AggSem defined) {
	assert(aggsolverpresent);

	if (modes().verbosity >= 7) {
		reportf("Adding aggregate with info ");
		gprintLit(head);
		reportf(", %d, %d, %s, %d, %s \n", setid, bound, boundsign==LB?"lower":"greater", type, defined==DEF?"defined":"completion");
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

bool PCSolver::addCPBinaryRel(Lit head, int groundname, MINISAT::EqType rel,
		int bound) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPBinaryRelVar(Lit head, int groundname, MINISAT::EqType rel,
		int groundname2) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSum(Lit head, vector<int> termnames, MINISAT::EqType rel,
		int bound) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSum(Lit head, vector<int> termnames, vector<int> mult,
		MINISAT::EqType rel, int bound) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSumVar(Lit head, vector<int> termnames,
		MINISAT::EqType rel, int rhstermname) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPSumVar(Lit head, vector<int> termnames, vector<int> mult,
		MINISAT::EqType rel, int rhstermname) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPCount(vector<int> termnames, int value,
		MINISAT::EqType rel, int rhstermname) {
	throw idpexception("CP-support is not compiled in.\n");
}

bool PCSolver::addCPAlldifferent(const vector<int>& termnames) {
	throw idpexception("CP-support is not compiled in.\n");
}

void PCSolver::addForcedChoices(const vec<Lit>& forcedchoices){
	if(forcedchoices.size()!=0){
		getSolver()->addForcedChoices(forcedchoices);
	}
}

/*
 * Returns "false" if UNSAT was already found, otherwise "true"
 */
bool PCSolver::finishParsing() {
	init = false;

	//important to call definition solver last
	if (aggsolverpresent) {
		bool unsat;
		getAggSolver()->finishParsing(aggsolverpresent, unsat);
		if(unsat){
			return false;
		}
	}
	if (idsolverpresent) {
		idsolverpresent = getIDSolver()->finishECNF_DataStructures();
		if (idsolverpresent) {
			if (!getIDSolver()->initAfterSimplify()) {
				return false;
			}
		}
	}

	// Do all propagations that have already been done on the SAT-solver level.
	for(vector<Lit>::const_iterator i=initialprops.begin(); i<initialprops.end(); i++){
		if(propagate(*i) != nullPtrClause){
			return false;
		}
	}
	initialprops.clear();
	if(propagateAtEndOfQueue() != nullPtrClause){
		return false;
	}

	if (!aggsolverpresent) {
		if (modes().verbosity > 0) {
			reportf("|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
		}
	}
	if (!idsolverpresent) {
		if (modes().verbosity > 0) {
			reportf("|    (there will be no definitional propagations)                             |\n");
		}
	}

	//TODO later modes.mnmz, modes.cp

	// Pre processing
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

void PCSolver::resetIDSolver() {
	idsolverpresent = false;
}

/**********************
 * AGGSOLVER SPECIFIC *
 **********************/

/**
 * Returns OWNING pointer (faster).
 */
rClause PCSolver::getExplanation(Lit l) {
	if (modes().verbosity > 2) {
		reportf("Find T-theory explanation for ");
		gprintLit(l);
		reportf("\n");
	}

	rClause explan = nullPtrClause;
	if(aggsolverpresent && explan == nullPtrClause){
		explan = getAggSolver()->getExplanation(l);
	}

	assert(explan!=nullPtrClause);

	return explan;
}

/*
 * SAT SOLVER SPECIFIC
 */

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
void PCSolver::newDecisionLevel(){
	//reportf("ADD DECISION LEVEL %d\n", ++decisionlevels);
	if(idsolverpresent){
		getIDSolver()->newDecisionLevel();
	}
	if(aggsolver){
		getAggSolver()->newDecisionLevel();
	}
}

//TODO implementeer ze hier allemaal
void PCSolver::backtrackDecisionLevel(int levels){
	for(int i=0; i<levels; i++){
		if(aggsolver){
			getAggSolver()->backtrackDecisionLevel();
		}
	}
	//reportf("Backtrack %d levels\n", levels);
	/*for(int i=0; i<levels; i++){
		//reportf("REMOVE DECISION LEVEL %d\n", --decisionlevels);
	}*/
}

/**
 * Returns not-owning pointer
 */
//FIXME: maybe let all lower ones return owning pointer, so only one reference to addlearnedclause?
rClause PCSolver::propagate(Lit l) {
	if(init){
		initialprops.push_back(l);
		return nullPtrClause;
	}

	//reportf("PROPAGATION LEVEL %d\n", getSolver()->getLevel(var(l)));

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
	if(simp && idsolverpresent){
		simp = getIDSolver()->initAfterSimplify();
	}
	return simp;
}

//TODO all models are kept in memory until the end, even if a method is called that does not return the models
//change the implementation to not save the models if not asked.
bool PCSolver::solve() {
	vec<Lit> assmpt;
	vec<vec<Lit> > models;
	return solve(assmpt, models);
}

bool PCSolver::solve(vec<vec<Lit> >& models) {
	vec<Lit> assmpt;
	return solve(assmpt, models);
}

//Straight to solver, search until a model is found
bool PCSolver::findModel(const vec<Lit>& assmpt) {
	return getSolver()->solve(assmpt);
}
//Straight to solver, do all propagations, but do not search
bool PCSolver::propagate(const vec<Lit>& assmpt) {
	return getSolver()->solve(assmpt, true);
}

bool PCSolver::solve(const vec<Lit>& assmpt, vec<vec<Lit> >& models) {
	bool solved = false;

	if (modes().verbosity >= 1) {
		reportf("============================[ Search Statistics ]==============================\n");
		reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
		reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
		reportf("===============================================================================\n");
	}

	modelsfound = 0;
	bool moremodels = true;

	//permanent assump = assertions: add as clause
	for (int i = 0; i < assmpt.size(); i++) {
		vec<Lit> ps;
		ps.push(assmpt[i]);
		addClause(ps);
	}

	if (optim != NONE) {
		vec<Lit> model;
		vec<Lit> assump;
		bool found = findOptimal(assump, model);

		if (found) {
			//put models in return models
			models.push();
			model.copyTo(models[models.size() - 1]);
		}
		solved = found;
	} else {
		while (moremodels && (nb_models == 0 || modelsfound < nb_models)) {
			vec<Lit> model;
			vec<Lit> assump;
			bool found = findNext(assump, model, moremodels);

			if (found) {
				//put models in return models
				models.push();
				model.copyTo(models[models.size() - 1]);
			}
		}

		if (modelsfound != 0 && !moremodels && nb_models != 1) {
			printf("| There are no more models                                                    |\n");
		}

		if (modelsfound == 0) {
			solved = false;
		} else if (nb_models == 0 || nb_models == modelsfound) {
			solved = true;
		} else {
			solved = false;
		}
	}

	if (modes().verbosity >= 1) {
		reportf("===============================================================================\n");
		getSolver()->printStatistics();
		if (idsolverpresent) {
			getIDSolver()->printStatistics();
		}
		if(aggsolverpresent){
			getAggSolver()->printStatistics();
		}
	}
	return solved;
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
	bool rslt = findModel(assmpt);

	if (!rslt) {
		moremodels = false;
		return false;
	}

	modelsfound++;

	m.clear();

	for (uint64_t i = 0; i < nVars(); i++) {
		if (value(i) == l_True) {
			m.push(mkLit(i, false));
		} else if (value(i) == l_False) {
			m.push(mkLit(i, true));
		}
	}

	if (nb_models != 1) {
		printf("| %4d model%s found                                                           |\n",
					modelsfound, modelsfound > 1 ? "s" : " ");
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
	//add all choice literals
	vector<Lit> v = getSolver()->getDecisions();
	for (vector<Lit>::const_iterator i = v.begin(); i < v.end(); i++) {
		invalidation.push(~(*i));
	}
	//add all assumptions
	/*for (int i = 0; i < assmpt.size(); i++){
	 learnt.push(~assmpt[i]);
	 }*/
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
	//FIXME: do not backtrack to 0, but do analyzefinal on learnt to check to which level to backtrack.
	//for subsetminimize this is not so clear, because assumptions have to be added too, so maybe there backtrack to 0 is necessary (for unit propagation before search)
	getSolver()->cancelUntil(0);

	if (modes().verbosity >= 3) {
		reportf("Adding model-invalidating clause: [ ");
		gprintClause(learnt);
		reportf("]\n");
	}

	bool result = addClause(learnt);

	getSolver()->varDecayActivity();
	getSolver()->claDecayActivity();

	if (modes().verbosity >= 3) {
		reportf("Model invalidated.\n");
	}

	return result;
}

/************************
 * OPTIMIZATION METHODS *
 ************************/

bool PCSolver::addMinimize(const vec<Lit>& lits, bool subsetmnmz){
	if (!modes().mnmz) {
		throw idpexception(
				"ERROR! Attempt at adding an optimization statement, though header "
					"did not contain \"mnmz\".\n");
	}
	if (lits.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}
	if (optim != NONE) {
		throw idpexception(
				"At most one set of literals to be minimized can be given.\n");
	}

	if (modes().verbosity >= 3) {
		reportf("Added minimization condition: %sinimize [", subsetmnmz?"Subsetm":"M");
		bool first = true;
		for(int i=0; i<lits.size(); i++){
			if(!first){
				reportf("%s", subsetmnmz?" ":"<");
			}
			first = false;
			gprintLit(lits[i]);
		}
		reportf("]\n");
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
		throw idpexception(
				"ERROR! Attempt at adding an optimization statement, though header "
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
		if (!currentoptimumfound && getSolver()->model[var(to_minimize[i])]
				== l_True) {
			if (modes().verbosity >= 1) {
				reportf("Current optimum is var %d\n", gprintVar(var(to_minimize[i])));
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
bool PCSolver::findOptimal(vec<Lit>& assmpt, vec<Lit>& m) {
	bool rslt = true, hasmodels = false, optimumreached = false;
	while (!optimumreached && rslt) {
		if (optim == SUMMNMZ) {
			assert(aggsolverpresent);
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			getAggSolver()->propagateMnmz(head);
		}
		rslt = getSolver()->solve(assmpt);

		if (rslt && !optimumreached) {
			if (!hasmodels) {
				hasmodels = true;
			}

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
				assmpt.clear();
				optimumreached = invalidateSubset(invalidation, assmpt);
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
				if (getSolver()->decisionLevel() != assmpt.size()) { //choices were made, so other models possible
					optimumreached = !invalidateModel(invalidation);
				} else {
					optimumreached = true;
				}
			}

			if (modes().verbosity > 0) {
				printf("Temporary model: \n");
				for (int i = 0; i < m.size(); i++) {
					printf("%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "": "-", gprintVar(var(m[i])));
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

void PCSolver::printChoiceMade(int level, Lit l) const {
	if (modes().verbosity >= 2) {
		reportf("Choice literal, dl %d, ", level);
		if (modsolverpresent) {
			reportf("mod s %zu", modsolver->getPrintId());
		}
		reportf(": ");
		gprintLit(l);
		reportf(".\n");
		//gprintLit(l); reportf(" ");
	}
}

vector<rClause> PCSolver::getClausesWhichOnlyContain(const vector<Var>& vars){
	return vector<rClause>();
	//return getSolver()->getClausesWhichOnlyContain(vars);
}
