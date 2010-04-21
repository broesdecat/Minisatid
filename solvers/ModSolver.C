#include "ModSolver.h"
#include <algorithm>

extern ECNF_mode modes;

void SolverData::finishParsing(){ //throws UNSAT
    //important to call definition solver last
	if(modes.aggr){
		modes.aggr = m->getAggSolver()->finishECNF_DataStructures();
	}
	if(modes.def){
		modes.def = m->getIDSolver()->finishECNF_DataStructures();
	}
	m->finishParsing();

	if(!modes.aggr){
		m->getAggSolver()->remove();
		greportf(1, "|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
	}
	if(!modes.def){
		m->getIDSolver()->remove();
		greportf(1, "|    (there will be no definitional propagations)                             |\n");
	}
	if(!modes.mnmz){
		//later
	}

	//FIXME: niet elke solver ondersteund dit? m->verbosity = verbosity;
	m->var_decay = modes.var_decay;
	m->random_var_freq = modes.random_var_freq;
	m->polarity_mode = modes.polarity_mode;
}

void copyToVec(const vec<Lit>& v, vector<Lit>& v2){
	for(int i=0; i<v.size(); i++){
	    v2.push_back(v[i]);
	}
}

void ModSolver::setChildren(const vector<Var>& a){
	//FIXME check that no ancestors become children or that some already have a parent
	for(vector<Var>::const_iterator i=a.begin(); i<a.end(); i++){
		children.push_back(*i);
		modhier.lock()->getModSolver(*i)->setParent(id);
	}
}

bool ModSolver::solve(){
	printModSolver(this);
	for(vector<int>::const_iterator i=getChildren().begin(); i<getChildren().end(); i++){
		printModSolver(modhier.lock()->getModSolver(*i));
	}

	return false;
}

bool ModSolverData::solve(){
	return m->solve();
}

bool ModSolverHier::solve(){
	return getModSolver(0)->solve();
}

void ModSolver::addClause(const vec<Lit>& lits){
	C r;
	copyToVec(lits, r.lits);

	/*reportf("Clause %d, %d: ", r.lits.size(), lits.size());
	for(int i=0; i<r.lits.size(); i++){
		reportf("%d ", var(r.lits[i])+1);
	}
	reportf("\n");*/

	theory.clauses.push_back(r);
}
void ModSolver::addSet(int set_id, const vec<Lit>& lits, const vector<Weight>& w){
	S s;
	s.id = set_id;
	copyToVec(lits, s.lits);
	for(int i=0; i<w.size(); i++){
		s.weights.push_back(w[i]);
	}

	//reportf("Set\n");

	theory.sets.push_back(s);
}
void ModSolver::addAggrExpr(int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined){
	A a;
	a.bound = bound;
	a.head = defn;
	a.defined = defined;
	a.set = set_id;
	a.type = type;
	a.lower = lower;

	//reportf("Aggr %d\n", a.head);

	atoms.push_back(AV(defn));
	theory.aggrs.push_back(a);
}



ModSolverHier::ModSolverHier(){

}

void ModSolverHier::initialize(){
	vector<int> l;
	solvers.push_back(new ExistentialModSolver(0, -1, l, shared_from_this()));
}

void ModSolverHier::addModSolver(int modid, Var head, bool exist, const vector<Var>& atoms){
	assert(modid>0);
	if(solvers.size()<modid+1){
		solvers.resize(modid+1, NULL);
	}
	assert(solvers[modid]==NULL);
	if(exist){
		solvers[modid] = new ExistentialModSolver(modid, head, atoms, shared_from_this());
	}else{
		solvers[modid] = new UniversalModSolver(modid, head, atoms, shared_from_this());
	}
}

void printModSolver(const ModSolver* m){
	reportf("ModSolver %d, parent %d, head %d, children ", m->getId(), m->getParentId(), gprintVar(m->getHead()));
	for(vector<int>::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
		reportf("%d ", *i);
	}
	reportf("\nModal atoms ");
	for(vector<AV>::const_iterator i=m->getAtoms().begin(); i<m->getAtoms().end(); i++){
		reportf("%d ", gprintVar((*i).atom));
	}
	reportf("\n");
	//print theory:
	for(vector<C>::const_iterator i=m->getTheory().clauses.begin(); i<m->getTheory().clauses.end(); i++){
		reportf("Clause ");
		for(vector<Lit>::const_iterator j=(*i).lits.begin(); j<(*i).lits.end(); j++){
			gprintLit(*j);reportf(" ");
		}
		reportf("\n");
	}
	for(vector<S>::const_iterator i=m->getTheory().sets.begin(); i<m->getTheory().sets.end(); i++){
		reportf("Set %d, ", (*i).id);
		for(int j=0; j<(*i).lits.size(); j++){
			gprintLit((*i).lits[j]);reportf("=%s", printWeight((*i).weights[j]).c_str());
		}
		reportf("\n");
	}
	for(vector<A>::const_iterator i=m->getTheory().aggrs.begin(); i<m->getTheory().aggrs.end(); i++){
		reportf("Aggr set %d, head %d, bound %s \n", (*i).set, (*i).head, printWeight((*i).bound).c_str());
		//FIXME not finished
	}
}

///**
// * Check if l is present in this modsolver as head or rigid atom.
// * 		If not, return
// * 		Else, set their new value and check for propagation
// *
// * Propagation:
// * 		forall and head true: find all models of constraint theory, and the modal theory has to be satisfied
// * 							for each of them
// * 		forall and head false: for at least one model of the constraint theory, the modal theory should be
// * 							violated
// *
// * 		exists and head true: find a model of constraint theory + modal theory
// * 		exists and head false: find constraint theory + modal theory unsat
// */
//Clause* MODSolver::propagate(Lit l){
//	Clause* confl = NULL;
//
//	bool found = false;
//	if(var(l)==head.atom){
//		head.value = sign(l)?l_False:l_True;
//		found = true;
//	}
//	for(int i=0; i<rigidatoms.size(); i++){
//		if(rigidatoms[i].atom==var(l)){
//			rigidatoms[i].value = sign(l)?l_False:l_True;
//			break;
//		}
//		found = true;
//	}
//	if(!found){
//		return confl;
//	}
//
//	//TODO unit propagation
//	//TODO propagate to lower modal operators
//	//TODO let solver propagate back to modal operator parent
//	//FIXME: make sure that only one search is done concurrently
//
//	if(canSearch()){
//		if(forall){
//			Solver* constr = initializeConstrSolver();
//			vec<Lit> assumpts, model;
//			//TODO select relevant part of rigid atoms
//			for(vector<AV>::iterator i=rigidatoms.begin(); i!=rigidatoms.end(); i++){
//				assert((*i).value!=l_Undef);
//				assumpts.push(Lit((*i).atom, (*i).value==l_True?false:true));
//			}
//			bool hasnextmodel = true, allsatisfied = true;
//			while(hasnextmodel && allsatisfied){
//				model.clear();
//				if (constr->simplify()){
//					hasnextmodel = constr->findNext(assumpts, model);
//				}
//				if(model.size()!=0){
//					Solver* modal = initializeModalSolver();
//					vec<Lit> fullmodel;
//					//TODO select relevant part of model (possibly add more rigid ones)
//					if (modal->simplify()){
//						modal->findNext(model, fullmodel);
//					}
//					if(fullmodel.size()==0){
//						allsatisfied = false;
//					}
//				}
//			}
//			if((!allsatisfied && head.value==l_False) || (allsatisfied && head.value==l_True)){
//				printf("Satisfied");
//			}else{
//				printf("Not satisfied, backtrack");
//				//FIXME add backtrack clause
//			}
//		}else{
//			Solver* solver = initializeExistsSolver();
//			//TODO select relevant part of rigid atoms
//			vec<Lit> assumpts, model;
//			for(vector<AV>::iterator i=rigidatoms.begin(); i!=rigidatoms.end(); i++){
//				assert((*i).value!=l_Undef);
//				assumpts.push(Lit((*i).atom, (*i).value==l_True?false:true));
//			}
//			if (solver->simplify()){
//				solver->findNext(assumpts, model);
//			}
//			if((model.size()!=0 && head.value==l_True) || (model.size()==0 && head.value==l_False)){
//				printf("Satisfied");
//			}else{
//				printf("Not satisfied, backtrack");
//				//FIXME: add backtrack clause
//			}
//		}
//	}
//
//	return NULL;
//}
//
//bool MODSolver::canSearch(){
//	if(head.value==l_Undef){
//		return false;
//	}
//	for(int i=0; i<rigidatoms.size(); i++){
//		if(rigidatoms[i].value==l_Undef){
//			return false;
//		}
//	}
//	return true;
//}
//
//void MODSolver::backtrack(Lit l){
//	/**
//	 * forget derived rigid atoms and any search done after l
//	 */
//}
//Clause* MODSolver::getExplanation(Lit l){
//	/**
//	 * save an explanation for each derived literal, to allow an easy enough derivation
//	 */
//	return NULL;
//}
//
//void copyToVec(vector<Lit>& v, vec<Lit>& v2, Solver* S){
//	for(vector<Lit>::iterator j=v.begin(); j!=v.end(); j++){
//	    while (var(*j) >= S->nVars()) S->newVar();
//	    S->setDecisionVar(var(*j),true);
//		v2.push(*j);
//	}
//}
///*template<class T>
//void copyToVec(vector<T>& v, vec<T>& v2){
//	for(vector<T>::iterator j=v.begin(); j!=v.end(); j++){
//	    v2.push(*j);
//	}
//}*/
//void copyToVec(vector<int>& v, vec<int>& v2){
//	for(vector<int>::iterator j=v.begin(); j!=v.end(); j++){
//	    v2.push(*j);
//	}
//}
///*void copyToVec(vector<Weight>& v, vec<Weight>& v2){
//	for(vector<Weight>::iterator j=v.begin(); j!=v.end(); j++){
//	    v2.push(*j);
//	}
//}*/
//
//Solver* MODSolver::initializeExistsSolver(){
//	Theory t;
//
//	Theory t2 = constrtheory;
//	t.clauses.insert(t.clauses.end(), t2.clauses.begin(), t2.clauses.end());
//	t.rules.insert(t.rules.end(), t2.rules.begin(), t2.rules.end());
//	t.aggrs.insert(t.aggrs.end(), t2.aggrs.begin(), t2.aggrs.end());
//	t.sets.insert(t.sets.end(), t2.sets.begin(), t2.sets.end());
//	t2 = modaltheory;
//	t.clauses.insert(t.clauses.end(), t2.clauses.begin(), t2.clauses.end());
//	t.rules.insert(t.rules.end(), t2.rules.begin(), t2.rules.end());
//	t.aggrs.insert(t.aggrs.end(), t2.aggrs.begin(), t2.aggrs.end());
//	t.sets.insert(t.sets.end(), t2.sets.begin(), t2.sets.end());
//
//	return initializeSolver(t);
//}
//Solver* MODSolver::initializeConstrSolver(){
//	return initializeSolver(constrtheory);
//}
//Solver* MODSolver::initializeModalSolver(){
//	return initializeSolver(modaltheory);
//}
//
//Solver* MODSolver::initializeSolver(Theory& t){
//	Solver* solver = initSolver();
//
//	for(vector<C>::iterator i=t.clauses.begin(); i!=t.clauses.end(); i++){
//		vec<Lit> lits;
//		copyToVec((*i).lits, lits, solver);
//		solver->addClause(lits);
//	}
//
//	IDSolver* idsolver = solver->getIDSolver();
//	for(vector<R>::iterator i=t.rules.begin(); i!=t.rules.end(); i++){
//		vec<Lit> lits;
//		copyToVec((*i).lits, lits, solver);
//		idsolver->addRule((*i).conj, lits);
//	}
//
//	AggSolver* aggsolver = solver->getAggSolver();
//	for(vector<S>::iterator i=t.sets.begin(); i!=t.sets.end(); i++){
//		vec<Lit> lits;
//		copyToVec((*i).lits, lits, solver);
//		vec<Weight> weights;
//		copyToVec((*i).weights, weights);
//		aggsolver->addSet((*i).id, lits, weights);
//	}
//	for(vector<A>::iterator i=t.aggrs.begin(); i!=t.aggrs.end(); i++){
//		aggsolver->addAggrExpr((*i).head, (*i).set, (*i).bound, (*i).lower, (*i).type, (*i).defined);
//	}
//
//	if(params.aggr && !aggsolver->finishECNF_DataStructures()){
//		solver->setAggSolver(NULL);
//		idsolver->setAggSolver(NULL);
//		delete aggsolver;
//	}
//	if(params.def && !idsolver->finishECNF_DataStructures()){
//		solver->setIDSolver(NULL);
//		aggsolver->setIDSolver(NULL);
//		delete idsolver;
//	}
//	solver->finishParsing();
//
//	return solver;
//}
//
//Solver* MODSolver::initSolver(){
//	Solver*		S 	= new Solver();
//	IDSolver*	TS 	= new IDSolver();
//	AggSolver*	AggS = new AggSolver();
//	S->setIDSolver(TS);
//	S->setAggSolver(AggS);
//	TS->setSolver(S);
//	TS->setAggSolver(AggS);
//	AggS->setSolver(S);
//	AggS->setIDSolver(TS);
//	return S;
//}
//
//void MODSolver::finishDatastructures(){
//	sort(modalatoms.begin(), modalatoms.end());
//	for(vector<MODSolver*>::iterator i=beginConstrChildren(); i!=endConstrChildren(); i++){
//		(*i)->finishDatastructures();
//	}
//	for(vector<MODSolver*>::iterator i=beginModalChildren(); i!=endModalChildren(); i++){
//		(*i)->finishDatastructures();
//	}
//}
//
