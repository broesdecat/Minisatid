/*
 * MODSolver.cpp
 *
 *  Created on: Feb 24, 2010
 *      Author: broes
 */

#include "MODSolver.h"
#include <algorithm>

Parameters params;

MODSolver::MODSolver():head(AV(0)) {
}

MODSolver::~MODSolver() {

}

void MODSolver::solve(){
	/*if (!S->simplify()){
		if (verbosity>=1) {
			reportf("===============================================================================\n");
			reportf("Solved by unit propagation\n");
		}
		if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
		printf("UNSATISFIABLE\n");
		exit(20);
	}

	S->nb_models=N;
	S->res=res;
	ret = S->solve();
	printStats(S);

	if(modes.def){
		delete TS;
	}
	if(modes.aggr){
		delete AggS;
	}*/
}

/**
 * Check if l is present in this modsolver as head or rigid atom.
 * 		If not, return
 * 		Else, set their new value and check for propagation
 */
Clause* MODSolver::propagate(Lit l){
	Clause* confl = NULL;

	bool found = false;
	if(var(l)==head.atom){
		head.value = sign(l)?l_False:l_True;
		found = true;
	}
	for(int i=0; i<rigidatoms.size(); i++){
		if(rigidatoms[i].atom==var(l)){
			rigidatoms[i].value = sign(l)?l_False:l_True;
			break;
		}
		found = true;
	}
	if(!found){
		return confl;
	}

	//TODO unit propagation

	if(canSearch()){
		Solver* constr = initializeSolver(true);
	}

	return NULL;
}

bool MODSolver::canSearch(){
	if(head.value==l_Undef){
		return false;
	}
	for(int i=0; i<rigidatoms.size(); i++){
		if(rigidatoms[i].value==l_Undef){
			return false;
		}
	}
	return true;
}

void MODSolver::backtrack(Lit l){
	/**
	 * forget derived rigid atoms and any search done after l
	 */
}
Clause* MODSolver::getExplanation(Lit l){
	/**
	 * save an explanation for each derived literal, to allow an easy enough derivation
	 */
	return NULL;
}

void copyToVec(vector<Lit>& v, vec<Lit>& v2, Solver* S){
	for(vector<Lit>::iterator j=v.begin(); j!=v.end(); j++){
	    while (var(*j) >= S->nVars()) S->newVar();
	    S->setDecisionVar(var(*j),true);
		v2.push(*j);
	}
}
void copyToVec(vector<int>& v, vec<int>& v2){
	for(vector<int>::iterator j=v.begin(); j!=v.end(); j++){
	    v2.push(*j);
	}
}

Solver* MODSolver::initializeSolver(bool constr){
	Solver* solver = initSolver();
	vector<R> r;
	vector<A> a;
	vector<C> c;
	vector<S> s;

	if(constr){
		r = constrrules;
		c = constrclauses;
		s = constrsets;
		a = constraggrs;
	}else{
		r = modrules;
		c = modclauses;
		s = modsets;
		a = modaggrs;
	}

	for(vector<C>::iterator i=c.begin(); i!=c.end(); i++){
		vec<Lit> lits;
		copyToVec((*i).lits, lits, solver);
		solver->addClause(lits);
	}

	IDSolver* idsolver = solver->getIDSolver();
	for(vector<R>::iterator i=r.begin(); i!=r.end(); i++){
		vec<Lit> lits;
		copyToVec((*i).lits, lits, solver);
		idsolver->addRule((*i).conj, lits);
	}

	AggSolver* aggsolver = solver->getAggSolver();
	for(vector<S>::iterator i=s.begin(); i!=s.end(); i++){
		vec<Lit> lits;
		copyToVec((*i).lits, lits, solver);
		vec<int> weights;
		copyToVec((*i).weights, weights);
		aggsolver->addSet((*i).id, lits, weights);
	}
	for(vector<A>::iterator i=a.begin(); i!=a.end(); i++){
		aggsolver->addAggrExpr((*i).head, (*i).set, (*i).bound, (*i).lower, (*i).type, (*i).defined);
	}

	if(!aggsolver->finishECNF_DataStructures()){
		solver->setAggSolver(NULL);
		idsolver->setAggSolver(NULL);
		delete aggsolver;
	}
	if(!idsolver->finishECNF_DataStructures()){
		solver->setIDSolver(NULL);
		aggsolver->setIDSolver(NULL);
		delete idsolver;
	}
	solver->finishParsing();

	return solver;
}

Solver* MODSolver::initSolver(){
	Solver*		S 	= new Solver();
	IDSolver*	TS 	= new IDSolver();
	AggSolver*	AggS = new AggSolver();
	S->setIDSolver(TS);
	S->setAggSolver(AggS);
	TS->setSolver(S);
	TS->setAggSolver(AggS);
	AggS->setSolver(S);
	AggS->setIDSolver(TS);
	return S;
}

void MODSolver::finishDatastructures(){
	sort(modalatoms.begin(), modalatoms.end());
}

void MODSolver::copyToVector(vec<Lit>& lits, vector<Lit> literals, bool constr){
	for(int i=0; i<lits.size(); i++){
		literals.push_back(lits[i]);
		if(!constr){
			modalatoms.push_back(AV(var(lits[i])));
		}
	}
}

void MODSolver::addRule(bool constr, bool conj, vec<Lit>& lits){
	vector<Lit> literals;
	copyToVector(lits, literals, constr);
	R r;
	r.lits = literals;
	r.conj = conj;
	if(constr){
		constrrules.push_back(r);
	}else{
		modrules.push_back(r);
	}
}
void MODSolver::addClause(bool constr, vec<Lit>& lits){
	vector<Lit> literals;
	copyToVector(lits, literals, constr);
	C r;
	r.lits = literals;
	if(constr){
		constrclauses.push_back(r);
	}else{
		modclauses.push_back(r);
	}
}
void MODSolver::addSet(bool constr, int set_id, vec<Lit>& lits, vec<int>& w){
	vector<Lit> literals;
	copyToVector(lits, literals, constr);
	vector<int> weights;
	for(int i=0; i<w.size(); i++){
		weights.push_back(w[i]);
	}
	S s;
	s.lits = literals;
	s.weights = weights;
	s.id = set_id;
	if(constr){
		constrsets.push_back(s);
	}else{
		modsets.push_back(s);
	}
}
void MODSolver::addAggrExpr(bool constr, int defn, int set_id, int bound, bool lower, AggrType type, bool defined){
	A a;
	a.bound = bound;
	a.head = defn;
	a.defined = defined;
	a.set = set_id;
	a.type = type;
	a.lower = lower;
	if(constr){
		constraggrs.push_back(a);
	}else{
		modalatoms.push_back(AV(defn));
		modaggrs.push_back(a);
	}
}

void MODSolver::subsetMinimize(vec<Lit>& lits){

}
