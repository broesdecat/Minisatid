#include "ModSolver.h"
#include <algorithm>

extern ECNF_mode modes;

ModSolver::ModSolver(bool neg, int id, Var head, const vector<Var>& a, shared_ptr<ModSolverHier> mh):negated(neg),id(id),head(head), modhier(mh){
	for(int i=0; i<a.size(); i++){
		atoms.push_back(AV(a[i]));
	}

	solver = shared_ptr<Solver>(new Solver());
	idsolver = shared_ptr<IDSolver>(new IDSolver());
	aggsolver = shared_ptr<AggSolver>(new AggSolver());

	solver->setIDSolver(idsolver);
	solver->setAggSolver(aggsolver);
	idsolver->setSolver(solver);
	idsolver->setAggSolver(aggsolver);
	aggsolver->setSolver(solver);
	aggsolver->setIDSolver(idsolver);
}

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

void ModSolver::addClause(vec<Lit>& lits){
	solver->addClause(lits);
}

void ModSolver::addRule(bool conj, vec<Lit>& lits){
	idsolver->addRule(conj,lits);
}

void ModSolver::addSet(int set_id, vec<Lit>& lits, vector<Weight>& w){
	aggsolver->addSet(id, lits, w);
}
void ModSolver::addAggrExpr(int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined){
	aggsolver->addAggrExpr(defn, set_id, bound, lower, type, defined);
}



ModSolverHier::ModSolverHier(){

}

void ModSolverHier::initialize(){
	vector<int> l;
	solvers.push_back(new ModSolver(false, 0, -1, l, shared_from_this()));
}

void ModSolverHier::addModSolver(int modid, Var head, bool neg, const vector<Var>& atoms){
	assert(modid>0);
	if(solvers.size()<modid+1){
		solvers.resize(modid+1, NULL);
	}
	assert(solvers[modid]==NULL);
	solvers[modid] = new ModSolver(neg, modid, head, atoms, shared_from_this());
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
/*	for(vector<C>::const_iterator i=m->getTheory().clauses.begin(); i<m->getTheory().clauses.end(); i++){
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
	}*/
}
