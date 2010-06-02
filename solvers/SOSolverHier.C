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

void ModSolverData::setNbModels(int nb){
	solvers[0]->setNbModels(nb);
}

void ModSolverData::setRes(FILE* f){
	solvers[0]->setRes(f);
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
	solvers.push_back(new ModSolver(0, -1, shared_from_this()));
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

bool ModSolverData::addChild(modindex parent, modindex child, Lit h){
	if(!existsModSolver(parent)){
		reportf("No modal operator with id %d was defined! ", parent+1);
		exit(1);
	}
	if(existsModSolver(child)){
		reportf("Modal operator with id %d was already defined! ", child+1);
		exit(1);
	}
	if(sign(h)){
		reportf("Modal operator %d has a negative head. This is not allowed.", child+1);
		exit(1);
	}
	if(solvers.size()<child+1){
		solvers.resize(child+1, NULL);
	}
	Var head = var(h);
	solvers[child] = new ModSolver(child, head, shared_from_this());
	solvers[child]->setParent(parent);
	return true;
}

bool ModSolverData::simplify(){
	return solvers[0]->simplify();
}

bool ModSolverData::solve(){
	return solvers[0]->propagateDownAtEndOfQueue()==0;
}

/**
 * Verifies whether the hierarchy is indeed a tree:
 * no loops exist
 * no-one is child of more than one solver
 * no solver has no parent unless it is the root
 *
 * Algorithm:
 * go through the tree BREADTH-FIRST, starting from the root
 * remember whether a solver has been seen and how many times
 */
void ModSolverData::verifyHierarchy(){
	vector<modindex> queue;
	vector<int> visitcount(solvers.size(), 0);
	queue.push_back(0);
	visitcount[0]++;
	while(queue.size()>0){
		modindex s = queue.back();
		queue.pop_back();
		pModSolver solver = getModSolver(s);
		for(vmodindex::const_iterator i=solver->getChildren().begin(); i<solver->getChildren().end(); i++){
			if(visitcount[*i]==0){
				queue.push_back(*i);
			}
			visitcount[*i]++;
		}
	}
	for(vmsolvers::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if(visitcount[(*i)->getId()]!=1 && *i!=NULL){
			reportf("The hierarchy of modal solvers does not form a tree. "
					"The Solver with id %d is %s.",
							(*i)->getPrintId(),
							visitcount[(*i)->getId()]==0?"not referenced":"referenced multiple times");
			exit(3);
		}
	}
}

bool ModSolverData::finishParsing(){
	verifyHierarchy();

	bool result = solvers[0]->finishParsing();

	if(modes.verbosity>=5){
		print(*this);
	}

	return result;
}

void print(const ModSolverData& d){
	reportf("Printing theory\n");
	print(*d.getModSolver((modindex)0));
	reportf("End of theory\n");
}
