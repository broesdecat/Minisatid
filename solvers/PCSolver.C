#include "PCSolver.h"
#include "Utils.h"

/******************
 * INITIALIZATION *
 ******************/

PCSolver::PCSolver(ECNF_mode modes):Data(),
			res(NULL), nb_models(1),
			modelsfound(0), modes(modes),
			optim(NONE),head(-1),
			aggsolverpresent(false), idsolverpresent(false), modsolverpresent(false){
	solver = new Solver(this);
	if(modes.def){
		idsolver = new IDSolver(this);
		idsolverpresent = true;
	}
	if(modes.aggr){
		aggsolver = new AggSolver(this);
		aggsolverpresent = true;
	}
	if(modes.def && modes.aggr){
		idsolver->setAggSolver(aggsolver);
	}

	//FIXME! also initialize parameters of Solver with modes
}

PCSolver::~PCSolver(){
	if(idsolverpresent){
		delete idsolver;
	}
	if(aggsolverpresent){
		delete aggsolver;
	}
	delete solver;
}

void PCSolver::setNbModels(int nb){
	nb_models=nb;
}

void PCSolver::setRes(FILE* f){
	res = f;
}

inline const pSolver& PCSolver::getSolver() const {
	return solver;
}

inline const pIDSolver& PCSolver::getIDSolver() const {
	return idsolver;
}

inline const pAggSolver& PCSolver::getAggSolver() const {
	return aggsolver;
}

inline const pModSolver& PCSolver::getModSolver() const {
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
int PCSolver::nVars() const{
	return getSolver()->nVars();
}

void PCSolver::addLearnedClause(Clause* c){
	getSolver()->addLearnedClause(c);
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

bool PCSolver::totalModelFound(){
	return getSolver()->totalModelFound();
}

int	PCSolver::getConflicts(){
	return getSolver()->conflicts;
}

void PCSolver::printClause(const Clause& c){
	getSolver()->printClause(c);
}

void PCSolver::varBumpActivity(Var v)	{
	getSolver()->varBumpActivity(v);
}


/************************
 * EXTENDING THE THEORY *
 ************************/

Var PCSolver::newVar(){
	Var v = getSolver()->newVar();
	addVar(v);
	return v;
}

void PCSolver::addVar(Var v){
	while (v >= nVars()){
		getSolver()->newVar(true, false);
		//FIXME: it would seem to have to be -1, but isnt the case?
		if(idsolverpresent){
			getIDSolver()->notifyVarAdded(nVars());
		}
		if(aggsolverpresent){
			getAggSolver()->notifyVarAdded(nVars());
		}
	}
	getSolver()->setDecisionVar(v,true); // S.nVars()-1   or   var
}

bool PCSolver::addClause(vec<Lit>& lits){
	return getSolver()->addClause(lits);
}

bool PCSolver::addRule(bool conj, vec<Lit>& lits){
	assert(idsolverpresent);
	return getIDSolver()->addRule(conj, lits);
}

bool PCSolver::addSet(int setid, vec<Lit>& lits, vector<Weight>& w){
	assert(aggsolverpresent);
	return getAggSolver()->addSet(setid, lits, w);
}

bool PCSolver::addAggrExpr(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	assert(aggsolverpresent);
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		exit(1);
	}
	return getAggSolver()->addAggrExpr(var(head), setid, bound, lower, type, defined);
}

bool PCSolver::finishParsing(){ //throws UNSAT
    //important to call definition solver last
	if(aggsolverpresent){
		modes.aggr = getAggSolver()->finishECNF_DataStructures();
		//
		vector<Lit> trail = getSolver()->getTrail();
		Clause* confl = NULL;
		for (int i=0; i<trail.size() && confl==NULL; i++){
			confl = getAggSolver()->propagate(trail[i]);
		}
		if(confl!=NULL){
			return false;
		}
	}
	if(idsolverpresent){
		modes.def = getIDSolver()->finishECNF_DataStructures();
	}

	if(!aggsolverpresent){
		delete aggsolver;
		if(modes.verbosity>0){
			reportf("|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
		}
	}
	if(!idsolverpresent){
		delete idsolver;
		if(modes.verbosity>0){
			reportf("|    (there will be no definitional propagations)                             |\n");
		}
	}
	if(!modes.mnmz){
		//TODO later
	}

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
	if(!getIDSolver()->isWellFoundedModel()){
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
	return aggsolverpresent?getAggSolver()->getExplanation(l):NULL;
}

void PCSolver::resetAggSolver(){
	aggsolverpresent = false;
}

/***********************
 * SAT SOLVER SPECIFIC *
 ***********************/

void PCSolver::backtrackRest(Lit l){
	if(aggsolverpresent){
		getAggSolver()->backtrack(l);
	}
	if(idsolverpresent){
		getIDSolver()->backtrack(l);
	}
	if(modsolverpresent){
		getModSolver()->backtrack(l);
	}
}

Clause* PCSolver::propagate(Lit l){
	Clause* confl = NULL;
	if(aggsolverpresent){
		confl = getAggSolver()->propagate(l);
	}
	if(idsolverpresent && confl == NULL){
		confl = getIDSolver()->propagate(l);
	}
	if(modsolverpresent && confl == NULL){
		confl = getModSolver()->propagateDown(l);
	}
	return confl;
}

Clause* PCSolver::propagateDefinitions(){
	if(!idsolverpresent){
		return NULL;
	}
	return getIDSolver()->propagateDefinitions();
}

/******************
 * SEARCH METHODS *
 ******************/

bool PCSolver::simplify(){
	return solver->simplify();
}

bool PCSolver::simplifyRest(){
	bool result = true;
	if(idsolverpresent){
		result = getIDSolver()->simplify();
	}
	if(modsolverpresent && result){
		result = getModSolver()->simplify();
	}
	return result;
}


bool PCSolver::solve() {
	bool solved = false;

	if (modes.verbosity >= 1) {
		reportf("============================[ Search Statistics ]==============================\n");
		reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
		reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
		reportf("===============================================================================\n");
	}

	modelsfound = 0;
	bool moremodels = true;

	if(optim!=NONE){
		vec<Lit> assmpt;
		vec<Lit> model;
		findOptimal(assmpt, model);
	}else{
		while(moremodels && (nb_models==0 || modelsfound<nb_models)){
			vec<Lit> assmpt;
			vec<Lit> model;
			moremodels = findNext(assmpt, model);
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

	if (modes.verbosity >= 1){
		reportf("===============================================================================\n");
	}
	return solved;
}

bool PCSolver::solve(const vec<Lit>& assmpt){
	return getSolver()->solve(assmpt);
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
 * FIXME: een mooier design maken zodat het duidelijk is naarwaar gebacktrackt moet worden (tot voor of tot
 * na de assumptions, afhankelijk van of ze voor alle modellen moeten gelden of alleen voor het huidige).
 */
bool PCSolver::findNext(const vec<Lit>& assmpt, vec<Lit>& m){
	bool rslt = solve(assmpt);

	if(rslt){
		modelsfound++;

		printModel();

		m.clear();
		for (int i = 0; i < nVars(); i++){
			if(value(i)==l_True){
				m.push(Lit(i, false));
			}else if(value(i)==l_False){
				m.push(Lit(i, true));
			}
		}

		//check if more models can exist
		if (getSolver()->getAllChoices().size() /*FIXME + assmpts.size() */!= 0) { //choices were made, so other models possible
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
	vector<Lit> v = getSolver()->getAllChoices();
	for (int i = 0; i < v.size(); i++){
		invalidation.push(~v[i]);
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

	//FIXME: hier werd soms verder gebacktrackt dan het laagste decision level (in de unit propagaties dus)
	//maar geen idee waarom dit nodig was. Mss toch eens nakijken?

	if (modes.verbosity>=3) {	reportf("Adding model-invalidating clause: [ "); }
	bool result = addClause(learnt);
	if (modes.verbosity>=3) {	reportf("]\n"); }

	getSolver()->varDecayActivity();
	getSolver()->claDecayActivity();

	return result;
}


void PCSolver::printModel() const{
	if (modelsfound==1) {
		fprintf(res==NULL?stdout:res, "SAT\n");
		if(modes.verbosity>=1){
			printf("SATISFIABLE\n");
		}
	}

	if(nb_models!=1){
		printf("%d model%s found.\n", modelsfound, modelsfound>1 ? "s" : "");
	}

	for (int i = 0; i < nVars(); i++){
		if (getSolver()->model[i] != l_Undef){
			fprintf(res==NULL?stdout:res, "%s%s%d", (i == 0) ? "" : " ", (getSolver()->model[i]== l_True) ? "" : "-", i + 1);
		}
	}
	fprintf(res==NULL?stdout:res, " 0\n");
}


/************************
 * OPTIMIZATION METHODS *
 ************************/

bool PCSolver::addMinimize(const vec<Lit>& lits, bool subset) {
	/*TODO if (!ecnf_mode.mnmz)
		reportf("ERROR! Attempt at adding a subset minimize statement, though ECNF specifiers did not contain \"mnmz\".\n"), exit(3);*/
	if (lits.size() == 0) {
		reportf("Error: The set of literals to be minimized is empty,\n");
		exit(3);
	}
	if (optim!=NONE) {
		reportf("At most one set of literals to be minimized can be given.\n");
		exit(3);
	}

	if(subset){
		optim = SUBSETMNMZ;
	}else{
		optim = MNMZ;
	}

	for (int i = 0; i < lits.size(); i++){
		to_minimize.push(lits[i]);
	}

	return true;
}

bool PCSolver::addSumMinimize(const Var head, const int setid){
	/*TODO if (!ecnf_mode.mnmz)
		reportf("ERROR! Attempt at adding a subset minimize statement, though ECNF specifiers did not contain \"mnmz\".\n"), exit(3);*/
	if (optim!=NONE) {
		reportf("Only one optimization statement is possible.\n");
		exit(3);
	}

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
			reportf("Current optimum is var %d\n", gprintVar(var(to_minimize[i])));
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
			for (int i = 0; i < nVars(); i++){
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
				if (getSolver()->getAllChoices().size() /*FIXME + assmpts.size() */!= 0) { //choices were made, so other models possible
					optimumreached = !invalidateModel(invalidation);
				}else{
					optimumreached = true;
				}
			}

			if(modes.verbosity>0){
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
		for (int i = 0; i < nVars(); i++){
			fprintf(res==NULL?stdout:res, "%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "" : "-", i + 1);
		}
		fprintf(res==NULL?stdout:res, " 0\n");

		modelsfound++;
	}

	return optimumreached;
}

