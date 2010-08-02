/************************************************************************************[PCSolver.hpp]
Copyright (c) 2009-2010, Broes De Cat

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
#include "solvers/pcsolver/PCSolver.hpp"
#include "solvers/utils/Utils.hpp"

/******************
 * INITIALIZATION *
 ******************/

int PCSolver::getModPrintID() const{
	if(modsolver!=NULL){
		return (int)modsolver->getPrintId();
	}
	return 0;
}

//Has to be value copy of modes!
PCSolver::PCSolver(ECNF_mode modes):Data(modes),
			solver(NULL), idsolver(NULL), aggsolver(NULL), modsolver(NULL), cpsolver(NULL),
			aggcreated(false), idcreated(false), cpcreated(false),
			aggsolverpresent(false), idsolverpresent(false), modsolverpresent(false), cpsolverpresent(false),
			nb_models(modes.nbmodels),
			modelsfound(0),
			optim(NONE),head(-1){
	solver = new Solver(this);
	if(modes.def){
		idsolver = new IDSolver(this);
		idcreated = true;
	}
	idsolverpresent = idcreated;
	if(modes.aggr){
		aggsolver = new AggSolver(this);
		aggcreated = true;
	}
	aggsolverpresent = aggcreated;
	if(modes.def && modes.aggr){
		idsolver->setAggSolver(aggsolver);
	}
	if(modes.cp){
		cpsolver = new CPSolver(this);
		cpcreated = true;
	}
	cpsolverpresent = cpcreated;

	//TODO depends on sat solver!
	//solver->maxruntime = modes.maxruntime;
	//solver->polarity_mode = modes.polarity_mode;
	solver->random_var_freq = modes.random_var_freq;
	solver->verbosity = modes.verbosity;
	solver->var_decay = modes.var_decay;
}

PCSolver::~PCSolver(){
	if(idcreated){
		delete idsolver;
	}
	if(aggcreated){
		delete aggsolver;
	}
	if(cpcreated){
		delete cpsolver;
	}
	delete solver;
}

void PCSolver::setNbModels(int nb){
	nb_models=nb;
}

inline pSolver PCSolver::getSolver() const {
	return solver;
}

inline pIDSolver PCSolver::getIDSolver() const {
	return idsolver;
}

inline pCPSolver PCSolver::getCPSolver() const {
	return cpsolver;
}

inline pAggSolver PCSolver::getAggSolver() const {
	return aggsolver;
}

inline pModSolver PCSolver::getModSolver() const {
	return modsolver;
}

CPSolver const * PCSolver::getCCPSolver() const {
	return cpsolver;
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

void PCSolver::setModSolver(pModSolver m){
	modsolver = m;
	modsolverpresent = true;
}

lbool PCSolver::value(Var x) const{
	return getSolver()->value(x);
}

lbool PCSolver::value(Lit p) const{
	return getSolver()->value(p);
}

uint64_t PCSolver::nVars() const{
	return getSolver()->nbVars();
}

void PCSolver::addLearnedClause(CCC c){
	if(c->size()>1){
		getSolver()->addLearnedClause(c);
	}else{
		assert(c->size()==1);
		//TODO maybe backtracking to 0 is not the best method.
		backtrackTo(0);
		vec<Lit> ps;
		ps.push(c->operator [](0));
		getSolver()->addClause(ps);
	}
}

void PCSolver::backtrackTo(int level){
	getSolver()->cancelUntil(level);
}

void PCSolver::setTrue(Lit p, CCC c){
	getSolver()->uncheckedEnqueue(p, c);
}

CCC PCSolver::makeClause(vec<Lit>& lits, bool b){
	return getSolver()->makeClause(lits, b);
}

int PCSolver::getLevel(int var) const	{
	return getSolver()->getLevel(var);
}

vector<Lit> PCSolver::getRecentAssignments() const{
	return getSolver()->getRecentAssignments();
}

int PCSolver::getNbDecisions() const{
	return getSolver()->decisionLevel();
}

vector<Lit> PCSolver::getDecisions() const{
	return getSolver()->getDecisions();
}

bool PCSolver::totalModelFound(){
	return getSolver()->totalModelFound();
}

uint64_t PCSolver::getConflicts() const{
	return getSolver()->conflicts;
}

void PCSolver::varBumpActivity(Var v)	{
	getSolver()->varBumpActivity(v);
}


/************************
 * EXTENDING THE THEORY *
 ************************/

Var PCSolver::newVar(){
	Var v = nVars();
	addVar(v);
	return v;
}

void PCSolver::addVar(Var v){
	assert(v>-1);
	while (v >= nVars()){
		getSolver()->newVar(true, false);
		if(idsolverpresent){
			getIDSolver()->notifyVarAdded(nVars());
		}
		if(aggsolverpresent){
			getAggSolver()->notifyVarAdded(nVars());
		}
	}
	getSolver()->setDecisionVar(v,true); // S.nVars()-1   or   var
}

void PCSolver::addVars(const vec<Lit>& a){
	for(int i=0; i<a.size(); i++){
		//reportf("Adding var %d\n", var(a[i]));
		addVar(var(a[i]));
	}
}

bool PCSolver::addClause(vec<Lit>& lits){
	if(modes().verbosity>=7){
		reportf("Adding clause:");
		for(int i=0; i<lits.size(); i++){
			reportf(" "); gprintLit(lits[i]);
		}
		reportf("\n");
	}
	addVars(lits);
	return getSolver()->addClause(lits);
}

bool PCSolver::addRule(bool conj, Lit head, const vec<Lit>& lits){
	assert(idsolverpresent);
	addVar(head);
	addVars(lits);
	return getIDSolver()->addRule(conj, head, lits);
}

bool PCSolver::addSet(int setid, const vec<Lit>& lits){
	assert(aggsolverpresent);
	addVars(lits);
	vector<Weight> w;
	w.resize(lits.size(), 1);
	return addSet(setid, lits, w);
}

bool PCSolver::addSet(int setid, const vec<Lit>& lits, const vector<Weight>& w){
	assert(aggsolverpresent);
	addVars(lits);
	return getAggSolver()->addSet(setid, lits, w);
}

bool PCSolver::addAggrExpr(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	assert(aggsolverpresent);

	if(modes().verbosity>=7){
		reportf("Adding aggregate with info "); gprintLit(head);
		reportf(", %d, %d, %s, %d, %s \n", setid, bound, lower?"lower":"greater", type, defined?"defined":"completion");
	}

	addVar(head);

	if(sign(head)){
		throw idpexception("Negative heads are not allowed.\n");
	}
	return getAggSolver()->addAggrExpr(var(head), setid, bound, lower, type, defined);
}

bool PCSolver::addIntVar(int groundname, int min, int max){
	assert(cpsolverpresent);
	getCPSolver()->addTerm(groundname, min, max);
	return true;
}

void PCSolver::checkHead(Lit head){
	addVar(head);
	if(sign(head)){
		throw idpexception("Negative heads are not allowed.\n");
	}
}

bool PCSolver::addCPBinaryRel(Lit head, int groundname, MINISAT::EqType rel, int bound){
	assert(cpsolverpresent);
	checkHead(head);
	getCPSolver()->addBinRel(groundname, rel, bound, var(head));
	return true;
}

bool PCSolver::addCPBinaryRelVar(Lit head, int groundname, MINISAT::EqType rel, int groundname2){
	assert(cpsolverpresent);
	checkHead(head);
	getCPSolver()->addBinRelVar(groundname, rel, groundname2, var(head));
	return true;
}

bool PCSolver::addCPSum(Lit head, vector<int> termnames, MINISAT::EqType rel, int bound){
	assert(cpsolverpresent);
	checkHead(head);
	getCPSolver()->addSum(termnames, rel, bound, var(head));
	return true;
}

bool PCSolver::addCPSum(Lit head, vector<int> termnames, vector<int> mult, MINISAT::EqType rel, int bound){
	assert(cpsolverpresent);
	checkHead(head);
	getCPSolver()->addSum(termnames, mult, rel, bound, var(head));
	return true;
}

bool PCSolver::addCPSumVar(Lit head, vector<int> termnames, MINISAT::EqType rel, int rhstermname){
	assert(cpsolverpresent);
	checkHead(head);
	getCPSolver()->addSum(termnames, rel, rhstermname, var(head));
	return true;
}

bool PCSolver::addCPSumVar(Lit head, vector<int> termnames, vector<int> mult, MINISAT::EqType rel, int rhstermname){
	assert(cpsolverpresent);
	checkHead(head);
	getCPSolver()->addSum(termnames, mult, rel, rhstermname, var(head));
	return true;
}

bool PCSolver::addCPCount(vector<int> termnames, int value, MINISAT::EqType rel, int rhstermname){
	assert(cpsolverpresent);
	getCPSolver()->addCount(termnames, rel, value, rhstermname);
	return true;
}

bool PCSolver::addCPAlldifferent(const vector<int>& termnames){
	assert(cpsolverpresent);
	return getCPSolver()->addAllDifferent(termnames);
}

/*
 * Returns "false" if UNSAT was already found, otherwise "true"
 */
bool PCSolver::finishParsing(){
    //important to call definition solver last
	if(aggsolverpresent){
		aggsolverpresent = getAggSolver()->finishECNF_DataStructures();
		//
		vector<Lit> trail = getSolver()->getTrail();
		CCC confl = NULL;
		for (vector<Lit>::const_iterator i=trail.begin(); i<trail.end() && confl==NULL; i++){
			confl = getAggSolver()->propagate(*i);
		}
		if(confl!=NULL){
			return false;
		}
	}
	if(cpsolverpresent){
		cpsolverpresent = getCPSolver()->finishParsing();
		vector<Lit> trail = getSolver()->getTrail();
		CCC confl = NULL;
		for (vector<Lit>::const_iterator i=trail.begin(); i<trail.end() && confl==NULL; i++){
			confl = getCPSolver()->propagate(*i);
		}
		if(confl!=NULL){
			return false;
		}
	}
	if(idsolverpresent){
		idsolverpresent = getIDSolver()->finishECNF_DataStructures();
		if(idsolverpresent){
			//TODO this might not be the best choice to do this now, as at the start,
			//simplification is called twice! But it simplifies the solve algorithm and
			//allows to keep the sat solver the same.
			if(!getIDSolver()->initAfterSimplify()){
				return false;
			}
		}
	}

	if(!aggsolverpresent){
		if(modes().verbosity>0){
			reportf("|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
		}
	}
	if(!cpsolverpresent){
		if(modes().verbosity>0){
			reportf("|    (there will be no CP           propagations)                             |\n");
		}
	}
	if(!idsolverpresent){
		if(modes().verbosity>0){
			reportf("|    (there will be no definitional propagations)                             |\n");
		}
	}

	//TODO later modes.mnmz, modes.cp

	return true;
}

/*********************
 * IDSOLVER SPECIFIC *
 *********************/

void PCSolver::removeAggrHead(Var x){
	if(idsolverpresent){
		getIDSolver()->removeAggrHead(x);
	}
}

void PCSolver::notifyAggrHead(Var x){
	if(idsolverpresent){
		getIDSolver()->notifyAggrHead(x);
	}
}

//if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status
lbool PCSolver::checkStatus(lbool status) const{
	if(!idsolverpresent || status!=l_True){
		return status;
	}
	if(modes().sem==WELLF && !getIDSolver()->isWellFoundedModel()){
		return l_False;
	}
	return status;
}

void PCSolver::resetIDSolver(){
	idsolverpresent = false;
}

/**********************
 * AGGSOLVER SPECIFIC *
 **********************/

CCC PCSolver::getExplanation(Lit l){
	if(modes().verbosity>2){
		reportf("Find an explanation for "); gprintLit(l); reportf("\n");
	}
	return aggsolverpresent?getAggSolver()->getExplanation(l):NULL;
}

/*
 * SAT SOLVER SPECIFIC
 */

void PCSolver::backtrackRest(Lit l){
	if(aggsolverpresent){
		getAggSolver()->backtrack(l);
	}
	if(idsolverpresent){
		getIDSolver()->backtrack(l);
	}
	if(cpsolverpresent){
		getCPSolver()->backtrack(l);
	}
	if(cpsolverpresent && getDecisions().back()==l){ //FIXME INCORRECT!
		getCPSolver()->backtrack();
	}
	if(modsolverpresent){
		getModSolver()->backtrackFromSameLevel(l);
	}
}

/**
 * Returns not-owning pointer
 */
//FIXME: maybe let all lower ones return owning pointer, so only one reference to addlearnedclause?
CCC PCSolver::propagate(Lit l){
	CCC confl = NULL;
	if(aggsolverpresent){
		confl = getAggSolver()->propagate(l);
	}
	if(idsolverpresent && confl == NULL){
		confl = getIDSolver()->propagate(l);
	}
	if(cpsolverpresent && confl == NULL){
		confl = getCPSolver()->propagate(l);
	}
	if(modsolverpresent && confl == NULL){
		confl = getModSolver()->propagate(l);
	}
	return confl;
}

/**
 * Returns not-owning pointer
 */
CCC PCSolver::propagateAtEndOfQueue(){
	CCC confl = NULL;
	if(idsolverpresent && confl == NULL){
		confl = getIDSolver()->propagateDefinitions();
	}
	if(cpsolverpresent && confl == NULL){
		confl = getCPSolver()->propagateAtEndOfQueue();
	}
	if(modsolverpresent && confl == NULL){
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
bool PCSolver::simplify(){
	return solver->simplify();
}

//TODO all models are kept in memory until the end, even if a method is called that does not return the models
//change the implementation to not save the models if not asked.
bool PCSolver::solve(){
	vec<Lit> assmpt;
	vec<vec<Lit> > models;
	return solveAll(assmpt, models);
}

bool PCSolver::solve(vec<vec<Lit> >& models){
	vec<Lit> assmpt;
	return solveAll(assmpt, models);
}

//Straight to solver
bool PCSolver::solvenosearch(const vec<Lit>& assmpt){
	return getSolver()->solve(assmpt, true);
}

//Straight to solver
bool PCSolver::solve(const vec<Lit>& assmpt){
	return getSolver()->solve(assmpt);
}

bool PCSolver::solveAll(vec<Lit>& assmpt, vec<vec<Lit> >& models){
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
	for(int i=0; i<assmpt.size(); i++){
		vec<Lit> ps;
		ps.push(assmpt[i]);
		addClause(ps);
	}

	if(optim!=NONE){
		vec<Lit> model;
		vec<Lit> assump;
		bool found = findOptimal(assump, model);

		if(found){
			//put models in return models
			models.push();
			model.copyTo(models[models.size()-1]);
		}
	}else{
		while(moremodels && (nb_models==0 || modelsfound<nb_models)){
			vec<Lit> model;
			vec<Lit> assump;
			bool found = findNext(assump, model, moremodels);

			if(found){
				//put models in return models
				models.push();
				model.copyTo(models[models.size()-1]);
			}
		}
	}

	if(modelsfound!=0 && !moremodels && nb_models!=1){
		printf("There are no more models.\n");
	}

	if(modelsfound==0){
		solved = false;
	}else if(nb_models==0 || nb_models==modelsfound){
		solved = true;
	}else{
		solved = false;
	}

	if (modes().verbosity >= 1){
		reportf("===============================================================================\n");
		getSolver()->printStatistics();
		if(idsolverpresent){
			getIDSolver()->printStatistics();
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
bool PCSolver::findNext(const vec<Lit>& assmpt, vec<Lit>& m, bool& moremodels){
	bool rslt = solve(assmpt);

	if(!rslt){
		moremodels = false;
		return false;
	}

	modelsfound++;

	m.clear();

	for (uint64_t i = 0; i < nVars(); i++){
		if(value(i)==l_True){
			m.push(mkLit(i, false));
		}else if(value(i)==l_False){
			m.push(mkLit(i, true));
		}
	}

	if(nb_models!=1){
		printf("%d model%s found.\n", modelsfound, modelsfound>1 ? "s" : "");
	}

	//check if more models can exist
	if (getSolver()->decisionLevel() != assmpt.size()) { //choices were made, so other models possible
		vec<Lit> invalidation;
		invalidate(invalidation);
		moremodels = invalidateModel(invalidation);
	}else{
		moremodels = false; //no more models possible
	}

	return true;
}


void PCSolver::invalidate(vec<Lit>& invalidation){
	// Add negation of model as clause for next iteration.
	//add all choice literals
	vector<Lit> v = getSolver()->getDecisions();
	for (vector<Lit>::const_iterator i = v.begin(); i < v.end(); i++){
		invalidation.push(~(*i));
	}
	//add all assumptions
	/*for (int i = 0; i < assmpt.size(); i++){
		learnt.push(~assmpt[i]);
	}*/
	// Remove doubles.
	sort(invalidation);
	Lit p = lit_Undef;
	int i=0, j=0;
	for (; i < invalidation.size(); i++){
		if (invalidation[i] != p){
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

	if (modes().verbosity>=3) {
		reportf("Adding model-invalidating clause: [ ");
		gprintClause(learnt);
		reportf("]\n");
	}

	bool result = addClause(learnt);

	getSolver()->varDecayActivity();
	getSolver()->claDecayActivity();

	return result;
}

/************************
 * OPTIMIZATION METHODS *
 ************************/

bool PCSolver::addMinimize(const vec<Lit>& lits, bool subset) {
	if (!modes().mnmz){
		throw idpexception("ERROR! Attempt at adding an optimization statement, though header "
				"did not contain \"mnmz\".\n");
	}
	if (lits.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}
	if (optim!=NONE) {
		throw idpexception("At most one set of literals to be minimized can be given.\n");
	}

	if(subset){
		optim = SUBSETMNMZ;
	}else{
		optim = MNMZ;
	}

	addVars(lits);
	for (int i = 0; i < lits.size(); i++){
		to_minimize.push(lits[i]);
	}

	return true;
}

bool PCSolver::addSumMinimize(const Var head, const int setid){
	if (!modes().mnmz){
		throw idpexception("ERROR! Attempt at adding an optimization statement, though header "
				"did not contain \"mnmz\".\n");
	}
	if (optim!=NONE) {
		throw idpexception("Only one optimization statement is allowed.\n");
	}

	addVar(head);
	optim = SUMMNMZ;
	this->head = head;
	vec<Lit> cl;
	cl.push(mkLit(head, false));
	bool notunsat = addClause(cl);
	//FIXME handle result;
	if(notunsat){
		assert(aggsolverpresent);
		notunsat = getAggSolver()->addMnmzSum(head, setid, true);
	}

	return notunsat;
}

bool PCSolver::invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt){
	int subsetsize = 0;

	for(int i=0; i<to_minimize.size(); i++){
		if(getSolver()->model[var(to_minimize[i])]==l_True){
			invalidation.push(~to_minimize[i]);
			subsetsize++;
		}else{
			assmpt.push(~to_minimize[i]);
		}
	}

	if(subsetsize==0){
		return true; //optimum has already been found!!!
	}else{
		return false;
	}
}

bool PCSolver::invalidateValue(vec<Lit>& invalidation){
	bool currentoptimumfound = false;

	for(int i=0; !currentoptimumfound && i<to_minimize.size(); i++){
		if(!currentoptimumfound && getSolver()->model[var(to_minimize[i])]==l_True){
			if(modes().verbosity>=1) {
				reportf("Current optimum is var %d\n", gprintVar(var(to_minimize[i])));
			}
			currentoptimumfound = true;
		}
		if(!currentoptimumfound){
			invalidation.push(to_minimize[i]);
		}
	}

	if(invalidation.size()==0){
		return true; //optimum has already been found!!!
	}else{
		return false;
	}
}


/*
 * If the optimum possible value is reached, the model is not invalidated. Otherwise, unsat has to be found first, so it is invalidated.
 * FIXME: add code that allows to reset the solver when the optimal value has been found, to search for more models with the same optimal value.
 *
 * Returns true if an optimal model was found
 */
bool PCSolver::findOptimal(vec<Lit>& assmpt, vec<Lit>& m){
	bool rslt = true, hasmodels = false, optimumreached = false;
	while(!optimumreached && rslt){
		if(optim==SUMMNMZ){
			assert(aggsolverpresent);
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			getAggSolver()->propagateMnmz(head);
		}
		rslt = getSolver()->solve(assmpt);

		if(rslt && !optimumreached){
			if(!hasmodels){
				hasmodels = true;
			}

			m.clear();
			int nvars = (int)nVars();
			for (int i = 0; i < nvars; i++){
				if(value(i)==l_True){
					m.push(mkLit(i, false));
				}else if(value(i)==l_False){
					m.push(mkLit(i, true));
				}
			}

			vec<Lit> invalidation;
			switch(optim){
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

			if(!optimumreached){
				if (getSolver()->decisionLevel() != assmpt.size()) { //choices were made, so other models possible
					optimumreached = !invalidateModel(invalidation);
				}else{
					optimumreached = true;
				}
			}

			if(modes().verbosity>0){
				printf("Temporary model: \n");
				for (int i = 0; i < m.size(); i++){
					printf("%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "" : "-", gprintVar(var(m[i])));
				}
				printf(" 0\n");
			}

		}else if(!rslt){
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

void PCSolver::printChoiceMade(int level, Lit l) const{
	if(modes().verbosity>=5){
		reportf("Choice literal at decisionlevel %d", level);
		if(modsolverpresent){
			reportf(" in modal solver %zu", modsolver->getPrintId());
		}
		reportf(": ");
		gprintLit(l);
		reportf(".\n");
	}
}
