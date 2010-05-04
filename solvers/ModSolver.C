#include "ModSolver.h"
#include <algorithm>

extern ECNF_mode modes;

ModSolver::ModSolver(modindex id, Lit head, const vector<Var>& a, shared_ptr<ModSolverData> mh):id(id),head(head), modhier(mh){
	//FIXME ID should be unique to the parent theory and as head of the modal solver. It should not occur in its children, lower or above the parent
	//FIXME there is no use for children rigid atoms that do not occur in the parent theory
	for(int i=0; i<a.size(); i++){
		atoms.push_back(AV(a[i]));
	}

	solver = new PCSolver(modes);
	//FIXME solver->setModSolver(this);
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

bool ModSolver::finishParsing(){
	bool result = solver->finishParsing();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->finishParsing();
	}

	return result;
}

bool ModSolver::simplify(){
	bool result = solver->simplify();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = modhier.lock()->getModSolver(*i)->simplify();
	}

	return result;
}

void ModSolver::addVar(int var){
	solver->addVar(var);
}

bool ModSolver::addClause(vec<Lit>& lits){
	return solver->addClause(lits);
}

bool ModSolver::addRule(bool conj, vec<Lit>& lits){
	return solver->addRule(conj,lits);
}

bool ModSolver::addSet(int setid, vec<Lit>& lits, vector<Weight>& w){
	return solver->addSet(setid, lits, w);
}

bool ModSolver::addAggrExpr(Lit head, int set_id, Weight bound, bool lower, AggrType type, bool defined){
	return solver->addAggrExpr(head, set_id, bound, lower, type, defined);
}


Clause* ModSolver::propagateDown(Lit l){
	Clause* confl = NULL;

	gprintLit(l); reportf(" propagated down into modal solver %d.\n", getId()+1);

	//Adapt head value
	bool contains = false;
	if(var(getHead())==var(l)){
		contains = true;
		assert(getHeadValue()==l_Undef);
		head.value = l==getHead()?l_True:l_False;
	}

	//adapt rigid atoms value
	for(vector<AV>::iterator i = atoms.begin(); i<atoms.end(); i++){
		if(var(l)==(*i).atom){
			contains = true;
			assert((*i).value==l_Undef);
			if(sign(l)){
				(*i).value = l_False;
			}else{
				(*i).value = l_True;
			}
		}
	}

	if(!contains){
		return confl;
	}

	//FIXME unit propagation

	//If all rigid atoms and head are known, do search in this solver
	bool allknown = true;
	vec<Lit> assumpts;
	for(vector<AV>::const_iterator j=getAtoms().begin(); allknown && j<getAtoms().end(); j++){
		if((*j).value==l_Undef){
			allknown = false;
		}else{
			//important: prevent double propagations! Only add what is not yet known by the solver
			if(solver->value((*j).atom)==l_Undef){
				assumpts.push(Lit((*j).atom, (*j).value==l_False));
			}
		}
	}
	if(!allknown){
		return confl;
	}
	bool result = solver->solve(assumpts);
	if((result && getHeadValue()!=l_True) || (!result && getHeadValue()!=l_False)){
		//conflict between head and body
		//FIXME good clause learning
		vec<Lit> confldisj;
		confldisj.push(~getHead());
		for(vector<AV>::const_iterator j=getAtoms().begin(); j<getAtoms().end(); j++){
			confldisj.push(Lit((*j).atom, (*j).value==l_True));
		}
		confl = Clause_new(confldisj, true);
	}
	solver->backtrackTo(0);
	return confl;
}

Clause* ModSolver::propagate(Lit l){
	Clause* confl = NULL;
	for(vmodindex::const_iterator i=getChildren().begin(); confl==NULL && i<getChildren().end(); i++){
		confl = modhier.lock()->getModSolver(*i)->propagateDown(l);
	}
	return confl;
}

void ModSolver::propagateUp(Lit l, modindex id){
	//FIXME save id for clause learning
	solver->setTrue(l);
}

void ModSolver::backtrack(Lit l){
	if(var(l)==var(getHead()) && getHeadValue()!=l_Undef){
		head.value = l_Undef;
		//FIXME: head is not allowed to occur in the theory or lower.
	}
	for(vector<AV>::iterator i=atoms.begin(); i<atoms.end(); i++){
		if((*i).atom==var(l)){
			if((*i).value!=l_Undef){
				(*i).value = l_Undef;
				solver->backtrackTo(solver->getLevel(var(l)));
				for(vmodindex::const_iterator j=getChildren().begin(); j<getChildren().end(); j++){
					modhier.lock()->getModSolver((*j))->backtrack(l);
				}
			}
			break;
		}
	}
}

void ModSolver::printModel(){
	solver->printModel();
}

void printModSolver(const ModSolver* m){
	reportf("ModSolver %d, parent %d, head ", m->getId(), m->getParentId() );
	gprintLit(m->getHead(), m->getHeadValue());
	reportf(", children ");
	for(vmodindex::const_iterator i=m->getChildren().begin(); i<m->getChildren().end(); i++){
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
