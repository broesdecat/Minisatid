#include "SOSolverHier.h"
#include "Utils.h"

bool ModSolverData::addClause(modindex modid, vec<Lit>& lits){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	pModSolver m = getModSolver(modid);
	return m->addClause(lits);
}
bool ModSolverData::addRule(modindex modid, bool conj, vec<Lit>& lits){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	pModSolver m = getModSolver(modid);
	return m->addRule(conj, lits);
}
bool ModSolverData::addSet(modindex modid, int setid, vec<Lit>& lits, vector<Weight>& w){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	pModSolver m = getModSolver(modid);
	return m->addSet(setid, lits, w);
}

bool ModSolverData::addAggrExpr(modindex modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		exit(1);
	}
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	pModSolver m = getModSolver(modid);
	return m->addAggrExpr(head, setid, bound, lower, type, defined);
}

void ModSolverData::addVar(Var v){
	for(vector<pModSolver>::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		(*i)->addVar(v);
	}
}

ModSolverData::ModSolverData():Data(){

}

ModSolverData::~ModSolverData(){
	deleteList<ModSolver>(solvers);
}

void ModSolverData::initialize(){
	vector<int> l;
	solvers.push_back(new ModSolver(0, Lit(-1), l, shared_from_this()));
}

bool ModSolverData::addModSolver(modindex modid, Lit head, const vector<Var>& atoms){
	assert(modid>0);
	if(solvers.size()<modid+1){
		solvers.resize(modid+1, NULL);
	}
	assert(solvers[modid]==NULL);
	solvers[modid] = new ModSolver(modid, head, atoms, shared_from_this());
	return false;
}

bool ModSolverData::addChildren(modindex modid, const vector<int>& children){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	for(vector<int>::const_iterator i=children.begin(); i<children.end(); i++){
		if(!existsModSolver(*i)){
			reportf("No modal operator with id %d was defined! ", *i+1);
			exit(1);
		}
	}
	pModSolver m = getModSolver(modid);
	m->setChildren(children);
	return false;
}

bool ModSolverData::simplify(){
	return solvers[0]->simplify();
}

bool ModSolverData::solve(){
	Clause* confl = solvers[0]->propagateDown(solvers[0]->getHead());
	if(confl!=NULL){
		return false;
	}

	solvers[0]->printModel();
	return true;
}

bool ModSolverData::finishParsing(){
	return solvers[0]->finishParsing();
}
