#include "ModSolver.h"
#include <algorithm>

extern ECNF_mode modes;

ModSolver::ModSolver(bool neg, int id, Var head, const vector<Var>& a, shared_ptr<ModSolverData> mh):negated(neg),id(id),head(head), modhier(mh){
	for(int i=0; i<a.size(); i++){
		atoms.push_back(AV(a[i]));
	}

	initializeSolvers(solver, idsolver, aggsolver);
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
	return getModSolver(0)->solve();
}

void ModSolver::addVar(int var){
	while (var >= solver->nVars()) solver->newVar();
	solver->setDecisionVar(var,true); // S.nVars()-1   or   var
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
