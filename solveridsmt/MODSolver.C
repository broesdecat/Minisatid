/*
 * MODSolver.cpp
 *
 *  Created on: Feb 24, 2010
 *      Author: broes
 */

#include "MODSolver.h"
#include <algorithm>

Parameters params;

MODSolver* MODSolver::root;

MODSolver*	MODSolver::getModalOperator(int id){
	if(id==0){
		return root;
	}else{
		return getModalOperator(id, *root);
	}
}

MODSolver*	MODSolver::getModalOperator(int id, MODSolver& m){
	MODSolver* found = NULL;
	for(vector<MODSolver*>::iterator i=m.beginModalChildren(); found==NULL && i!=m.endModalChildren(); i++){
		if((*i)->getID()){
			found = *i;
		}else{
			found = getModalOperator(id, **i);
		}
	}
	for(vector<MODSolver*>::iterator i=m.beginConstrChildren(); found==NULL && i!=m.endConstrChildren(); i++){
		if((*i)->getID()){
			found = *i;
		}else{
			found = getModalOperator(id, **i);
		}
	}
	return found;
}

MODSolver::MODSolver(int id):id(id),head(AV(-1)), forall(false) {
	if(id==0){
		assert(root==NULL);
		root = this;
	}
}

MODSolver::~MODSolver() {

}

/**
 * Check if l is present in this modsolver as head or rigid atom.
 * 		If not, return
 * 		Else, set their new value and check for propagation
 *
 * Propagation:
 * 		forall and head true: find all models of constraint theory, and the modal theory has to be satisfied
 * 							for each of them
 * 		forall and head false: for at least one model of the constraint theory, the modal theory should be
 * 							violated
 *
 * 		exists and head true: find a model of constraint theory + modal theory
 * 		exists and head false: find constraint theory + modal theory unsat
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
	//TODO propagate to lower modal operators
	//TODO let solver propagate back to modal operator parent
	//FIXME: make sure that only one search is done concurrently

	if(canSearch()){
		if(forall){
			Solver* constr = initializeConstrSolver();
			vec<Lit> assumpts, model;
			//TODO select relevant part of rigid atoms
			for(vector<AV>::iterator i=rigidatoms.begin(); i!=rigidatoms.end(); i++){
				assert((*i).value!=l_Undef);
				assumpts.push(Lit((*i).atom, (*i).value==l_True?false:true));
			}
			bool hasnextmodel = true, allsatisfied = true;
			while(hasnextmodel && allsatisfied){
				model.clear();
				if (constr->simplify()){
					hasnextmodel = constr->findNext(assumpts, model);
				}
				if(model.size()!=0){
					Solver* modal = initializeModalSolver();
					vec<Lit> fullmodel;
					//TODO select relevant part of model (possibly add more rigid ones)
					if (modal->simplify()){
						modal->findNext(model, fullmodel);
					}
					if(fullmodel.size()==0){
						allsatisfied = false;
					}
				}
			}
			if((!allsatisfied && head.value==l_False) || (allsatisfied && head.value==l_True)){
				printf("Satisfied");
			}else{
				printf("Not satisfied, backtrack");
				//FIXME add backtrack clause
			}
		}else{
			Solver* solver = initializeExistsSolver();
			//TODO select relevant part of rigid atoms
			vec<Lit> assumpts, model;
			for(vector<AV>::iterator i=rigidatoms.begin(); i!=rigidatoms.end(); i++){
				assert((*i).value!=l_Undef);
				assumpts.push(Lit((*i).atom, (*i).value==l_True?false:true));
			}
			if (solver->simplify()){
				solver->findNext(assumpts, model);
			}
			if((model.size()!=0 && head.value==l_True) || (model.size()==0 && head.value==l_False)){
				printf("Satisfied");
			}else{
				printf("Not satisfied, backtrack");
				//FIXME: add backtrack clause
			}
		}
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

Solver* MODSolver::initializeExistsSolver(){
	Theory t;

	Theory t2 = constrtheory;
	t.clauses.insert(t.clauses.end(), t2.clauses.begin(), t2.clauses.end());
	t.rules.insert(t.rules.end(), t2.rules.begin(), t2.rules.end());
	t.aggrs.insert(t.aggrs.end(), t2.aggrs.begin(), t2.aggrs.end());
	t.sets.insert(t.sets.end(), t2.sets.begin(), t2.sets.end());
	t2 = modaltheory;
	t.clauses.insert(t.clauses.end(), t2.clauses.begin(), t2.clauses.end());
	t.rules.insert(t.rules.end(), t2.rules.begin(), t2.rules.end());
	t.aggrs.insert(t.aggrs.end(), t2.aggrs.begin(), t2.aggrs.end());
	t.sets.insert(t.sets.end(), t2.sets.begin(), t2.sets.end());

	return initializeSolver(t);
}
Solver* MODSolver::initializeConstrSolver(){
	return initializeSolver(constrtheory);
}
Solver* MODSolver::initializeModalSolver(){
	return initializeSolver(modaltheory);
}

Solver* MODSolver::initializeSolver(Theory& t){
	Solver* solver = initSolver();

	for(vector<C>::iterator i=t.clauses.begin(); i!=t.clauses.end(); i++){
		vec<Lit> lits;
		copyToVec((*i).lits, lits, solver);
		solver->addClause(lits);
	}

	IDSolver* idsolver = solver->getIDSolver();
	for(vector<R>::iterator i=t.rules.begin(); i!=t.rules.end(); i++){
		vec<Lit> lits;
		copyToVec((*i).lits, lits, solver);
		idsolver->addRule((*i).conj, lits);
	}

	AggSolver* aggsolver = solver->getAggSolver();
	for(vector<S>::iterator i=t.sets.begin(); i!=t.sets.end(); i++){
		vec<Lit> lits;
		copyToVec((*i).lits, lits, solver);
		vec<int> weights;
		copyToVec((*i).weights, weights);
		aggsolver->addSet((*i).id, lits, weights);
	}
	for(vector<A>::iterator i=t.aggrs.begin(); i!=t.aggrs.end(); i++){
		aggsolver->addAggrExpr((*i).head, (*i).set, (*i).bound, (*i).lower, (*i).type, (*i).defined);
	}

	if(params.aggr && !aggsolver->finishECNF_DataStructures()){
		solver->setAggSolver(NULL);
		idsolver->setAggSolver(NULL);
		delete aggsolver;
	}
	if(params.def && !idsolver->finishECNF_DataStructures()){
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

void MODSolver::addChild(MODSolver* m, bool constr){
	if(constr){
		constrtheory.children.push_back(m);
	}else{
		modaltheory.children.push_back(m);
	}
}

void 	MODSolver::addRigidAtoms(vec<int>& atoms){
	for(int i=0; i<atoms.size(); i++){
		rigidatoms.push_back(atoms[i]);
	}
}

void MODSolver::finishDatastructures(){
	sort(modalatoms.begin(), modalatoms.end());
	for(vector<MODSolver*>::iterator i=beginConstrChildren(); i!=endConstrChildren(); i++){
		(*i)->finishDatastructures();
	}
	for(vector<MODSolver*>::iterator i=beginModalChildren(); i!=endModalChildren(); i++){
		(*i)->finishDatastructures();
	}
}

void MODSolver::addRule(bool constr, bool conj, vec<Lit>& lits){
	R r;
	copyToVector(lits, r.lits, constr);

	/*reportf("Rule %d, %d: ", r.lits.size(), lits.size());
	for(int i=0; i<r.lits.size(); i++){
		reportf("%d ", var(r.lits[i])+1);
	}
	reportf("\n");*/

	r.conj = conj;
	if(constr){
		constrtheory.rules.push_back(r);
	}else{
		modaltheory.rules.push_back(r);
	}
}
void MODSolver::addClause(bool constr, vec<Lit>& lits){
	C r;
	copyToVector(lits, r.lits, constr);

	/*reportf("Clause %d, %d: ", r.lits.size(), lits.size());
	for(int i=0; i<r.lits.size(); i++){
		reportf("%d ", var(r.lits[i])+1);
	}
	reportf("\n");*/

	if(constr){
		constrtheory.clauses.push_back(r);
	}else{
		modaltheory.clauses.push_back(r);
	}
}
void MODSolver::addSet(bool constr, int set_id, vec<Lit>& lits, vec<int>& w){
	S s;
	s.id = set_id;
	copyToVector(lits, s.lits, constr);
	for(int i=0; i<w.size(); i++){
		s.weights.push_back(w[i]);
	}

	//reportf("Set\n");

	if(constr){
		constrtheory.sets.push_back(s);
	}else{
		modaltheory.sets.push_back(s);
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

	//reportf("Aggr %d\n", a.head);

	if(constr){
		constrtheory.aggrs.push_back(a);
	}else{
		modalatoms.push_back(AV(defn));
		modaltheory.aggrs.push_back(a);
	}
}

void MODSolver::copyToVector(vec<Lit>& lits, vector<Lit>& literals, bool constr){
	for(int i=0; i<lits.size(); i++){
		literals.push_back(lits[i]);
		if(!constr){
			modalatoms.push_back(AV(var(lits[i])));
		}
	}
}
