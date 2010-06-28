#include "solvers/PCSolver.hpp"
#include "solvers/Utils.hpp"

/*SolverI::SolverI(PCSolver* const solver): pcsolver(solver){

};*/

/******************
 * INITIALIZATION *
 ******************/

int PCSolver::getModPrintID() const{
	if(modsolver!=NULL){
		return modsolver->getPrintId();
	}
	return -1;
}

//Has to be value copy of modes!
PCSolver::PCSolver(ECNF_mode modes):Data(modes),
			solver(NULL), idsolver(NULL), aggsolver(NULL), modsolver(NULL), cpsolver(NULL),
			aggcreated(false), idcreated(false), cpcreated(false),
			aggsolverpresent(false), idsolverpresent(false), modsolverpresent(false), cpsolverpresent(false),
			res(NULL), nb_models(modes.nbmodels),
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

	//solver->maxruntime = modes.maxruntime;
	solver->polarity_mode = modes.polarity_mode;
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

void PCSolver::setRes(FILE* f){
	res = f;
}

inline pSolver const PCSolver::getSolver() const {
	return solver;
}

inline pIDSolver const PCSolver::getIDSolver() const {
	return idsolver;
}

inline pCPSolver const PCSolver::getCPSolver() const {
	return cpsolver;
}

inline pAggSolver const PCSolver::getAggSolver() const {
	return aggsolver;
}

inline pModSolver const PCSolver::getModSolver() const {
	return modsolver;
}

Solver const * const PCSolver::getCSolver() const {
	return solver;
}

IDSolver const * const PCSolver::getCIDSolver() const {
	return idsolver;
}

CPSolver const * const PCSolver::getCCPSolver() const {
	return cpsolver;
}

AggSolver const * const PCSolver::getCAggSolver() const {
	return aggsolver;
}

ModSolver const * const PCSolver::getCModSolver() const {
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

void PCSolver::addLearnedClause(Clause* c){
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

void PCSolver::setTrue(Lit p, Clause* c){
	getSolver()->uncheckedEnqueue(p, c);
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
	uint64_t var = v;
	while (var >= nVars()){
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
		addVar(var(a[i]));
	}
}

bool PCSolver::addClause(vec<Lit>& lits){
	addVars(lits);
	return getSolver()->addClause(lits);
}

bool PCSolver::addRule(bool conj, vec<Lit>& lits){
	assert(idsolverpresent);
	addVars(lits);
	return getIDSolver()->addRule(conj, lits);
}

bool PCSolver::addSet(int setid, vec<Lit>& lits){
	assert(aggsolverpresent);
	addVars(lits);
	vector<Weight> w;
	w.resize(lits.size(), 1);
	return addSet(setid, lits, w);
}

bool PCSolver::addSet(int setid, vec<Lit>& lits, const vector<Weight>& w){
	assert(aggsolverpresent);
	addVars(lits);
	return getAggSolver()->addSet(setid, lits, w);
}

bool PCSolver::addAggrExpr(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	assert(aggsolverpresent);
	addVar(var(head));
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		throw idpexception();
	}
	return getAggSolver()->addAggrExpr(var(head), setid, bound, lower, type, defined);
}

bool PCSolver::finishParsing(){ //throws UNSAT
    //important to call definition solver last
	if(aggsolverpresent){
		aggsolverpresent = getAggSolver()->finishECNF_DataStructures();
		//
		vector<Lit> trail = getSolver()->getTrail();
		Clause* confl = NULL;
		for (vector<Lit>::const_iterator i=trail.begin(); i<trail.end() && confl==NULL; i++){
			confl = getAggSolver()->propagate(*i);
		}
		if(confl!=NULL){
			return false;
		}
	}
	if(idsolverpresent){
		idsolverpresent = getIDSolver()->finishECNF_DataStructures();
	}

	if(!aggsolverpresent){
		if(modes().verbosity>0){
			reportf("|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
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

Clause* PCSolver::getExplanation(Lit l){
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
	if(modsolverpresent){
		getModSolver()->backtrackFromSameLevel(l);
	}
}

/**
 * Returns not-owning pointer
 */
//FIXME: maybe let all lower ones return owning pointer, so only one reference to addlearnedclause?
Clause* PCSolver::propagate(Lit l){
	Clause* confl = NULL;
	if(aggsolverpresent){
		confl = getAggSolver()->propagate(l);
	}
	if(idsolverpresent && confl == NULL){
		confl = getIDSolver()->propagate(l);
	}
	if(modsolverpresent && confl == NULL){
		confl = getModSolver()->propagate(l);
	}
	return confl;
}

/**
 * Returns not-owning pointer
 */
Clause* PCSolver::propagateAtEndOfQueue(){
	Clause* confl = NULL;
	if(idsolverpresent && confl == NULL){
		confl = getIDSolver()->propagateDefinitions();
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

bool PCSolver::solve(){
	vec<Lit> assmpt;
	vector<vector<int> > models;
	return solveAll(assmpt, models);
}

bool PCSolver::solve(vector<vector<int> >& models){
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

bool PCSolver::solveAll(vec<Lit>& assmpt, vector<vector<int> >& models){
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
		findOptimal(assump, model);

		//put models in return models
		vector<int> modelasint;
		for(int i=0; i<model.size(); i++){
			int atom = var(model[i])+1;
			modelasint.push_back(sign(model[i])?-atom:atom);
		}
		models.push_back(modelasint);

	}else{
		while(moremodels && (nb_models==0 || modelsfound<nb_models)){
			vec<Lit> model;
			vec<Lit> assump;
			moremodels = findNext(assump, model);

			//put models in return models
			vector<int> modelasint;
			for(int i=0; i<model.size(); i++){
				int atom = var(model[i])+1;
				modelasint.push_back(sign(model[i])?-atom:atom);
			}
			models.push_back(modelasint);
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
	}
	return solved;
}


/**
 * Checks satisfiability of the theory.
 * If no model is found or no more models exist, false is returned. True otherwise
 * If a model is found, it is printed and returned in <m>, the theory is extended to prevent
 * 		the same model from being found again and
 * 		the datastructures are reset to prepare to find the next model
 */
/**
 * Important: assmpt are the first DECISIONS that are made. So they are not automatic unit propagations
 * and can be backtracked!
 */
bool PCSolver::findNext(const vec<Lit>& assmpt, vec<Lit>& m){
	bool rslt = solve(assmpt);

	if(rslt){
		modelsfound++;

		printModel();

		m.clear();
		for (uint64_t i = 0; i < nVars(); i++){
			if(value(i)==l_True){
				m.push(Lit(i, false));
			}else if(value(i)==l_False){
				m.push(Lit(i, true));
			}
		}

		//check if more models can exist
		if (getSolver()->decisionLevel() != assmpt.size()) { //choices were made, so other models possible
			vec<Lit> invalidation;
			invalidate(invalidation);
			rslt = invalidateModel(invalidation);
		}else{
			rslt = false; //no more models possible
		}
	}

	return rslt;
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
		reportf("ERROR! Attempt at adding an optimization statement, though header "
				"did not contain \"mnmz\".\n");
		throw idpexception();
	}
	if (lits.size() == 0) {
		reportf("Error: The set of literals to be minimized is empty,\n");
		throw idpexception();
	}
	if (optim!=NONE) {
		reportf("At most one set of literals to be minimized can be given.\n");
		throw idpexception();
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
		reportf("ERROR! Attempt at adding an optimization statement, though header "
				"did not contain \"mnmz\".\n");
		throw idpexception();
	}
	if (optim!=NONE) {
		reportf("Only one optimization statement is possible.\n");
		throw idpexception();
	}

	addVar(head);
	optim = SUMMNMZ;
	this->head = head;
	vec<Lit> cl;
	cl.push(Lit(head, false));
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
					m.push(Lit(i, false));
				}else if(value(i)==l_False){
					m.push(Lit(i, true));
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
	}

	return optimumreached;
}

void PCSolver::printModel() const{
	if (modelsfound==1) {
		fprintf(res==NULL?stdout:res, "SAT\n");
		if(modes().verbosity>=1){
			printf("SATISFIABLE\n");
		}
	}

	if(nb_models!=1){
		printf("%d model%s found.\n", modelsfound, modelsfound>1 ? "s" : "");
	}

	int nvars = (int)nVars();
	for (int i = 0; i < nvars; i++){
		if (getSolver()->model[i] != l_Undef){
			fprintf(res==NULL?stdout:res, "%s%s%d", (i == 0) ? "" : " ", (getSolver()->model[i]== l_True) ? "" : "-", i + 1);
		}
	}
	fprintf(res==NULL?stdout:res, " 0\n");
}

void PCSolver::printChoiceMade(int level, Lit l) const{
	if(modes().verbosity>=5){
		reportf("Choice literal at decisionlevel %d", level);
		if(modsolverpresent){
			reportf(" in modal solver %d", modsolver->getPrintId());
		}
		reportf(": ");
		gprintLit(l);
		reportf(".\n");
	}
}
