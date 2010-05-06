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

void ModSolverData::addVar(modindex modid, Var v){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	getModSolver(modid)->addVar(v);
}

ModSolverData::ModSolverData():Data(){

}

ModSolverData::~ModSolverData(){
	deleteList<ModSolver>(solvers);
}

void ModSolverData::initialize(){
	solvers.push_back(new ModSolver(0, Lit(-1), shared_from_this()));
}

void ModSolverData::addAtoms(modindex modid, const vector<Var>& atoms){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		exit(1);
	}
	getModSolver(modid)->addAtoms(atoms);
}

/*bool ModSolverData::addModSolver(modindex modid, Lit head){
	assert(modid>0);
	if(solvers.size()<modid+1){
		solvers.resize(modid+1, NULL);
	}
	assert(solvers[modid]==NULL);
	solvers[modid] = new ModSolver(modid, head, shared_from_this());
	return true;
}*/

bool ModSolverData::addChild(modindex parent, modindex child, Lit head){
	if(!existsModSolver(parent)){
		reportf("No modal operator with id %d was defined! ", parent+1);
		exit(1);
	}
	if(existsModSolver(child)){
		reportf("Modal operator with id %d was already defined! ", child+1);
		exit(1);
	}
	if(solvers.size()<child+1){
		solvers.resize(child+1, NULL);
	}
	solvers[child] = new ModSolver(child, head, shared_from_this());
	solvers[child]->setParent(parent);
	return true;
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
