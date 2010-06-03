#include "SOSolverHier.hpp"
#include "Utils.hpp"

void ModSolverData::checkexistsModSolver(modindex modid) const {
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		throw idpexception();
	}
}

/**
 * Try to add the clause as high up in the hierarchy as possible.
 *
 * How can this be done: if all literals of a clause are rigid atoms, then the clause
 * if effectively relevant to the parent modal operator.
 * The sign of the modal operators decides whether the clause has to be negated or not.
 * If it is too difficult too negate it, it is not pushed upwards.
 *
 * This is only possible if the sign of the modal operator is fixed. It is guaranteed that if
 * it is certainly fixed, the head will be known at this point in time.
 *
 * Currently done substitutions
 */
bool ModSolverData::addClause(modindex modid, vec<Lit>& lits){
	checkexistsModSolver(modid);
	modindex previd = modid, currentid = modid;
	pModSolver m = NULL;
	bool negated = false;
	while(true){
		m = getModSolver(currentid);
		bool alloccur = true;
		for(int i=0; alloccur && i<lits.size(); i++){
			bool seen = false;
			for(vector<AV>::const_iterator j=m->getAtoms().begin(); !seen && j<m->getAtoms().end(); j++){
				if((*j).atom==var(lits[i])){
					seen = true;
				}
			}
			if(!seen){
				alloccur = false;
			}
		}
		if(!alloccur){
			break;
		}
		if(m->getHeadValue()==l_Undef){
			break;
		}else if(m->getHeadValue()==l_False){
			negated = !negated;
		}
		int parentid = m->getParentId();
		if(parentid==-1){
			break;
		}
		currentid = parentid;
		if(!negated){
			 previd = currentid;
		}
	}
	if(negated){
		//reportf("orig %d => new %d\n", modid, previd);
		return getModSolver(previd)->addClause(lits);
	}else{
		//reportf("orig %d => new %d\n", modid, currentid);
		return getModSolver(currentid)->addClause(lits);
	}
}

bool ModSolverData::addRule(modindex modid, bool conj, vec<Lit>& lits){
	checkexistsModSolver(modid);
	pModSolver m = getModSolver(modid);
	return m->addRule(conj, lits);
}

bool ModSolverData::addSet(modindex modid, int setid, vec<Lit>& lits, vector<Weight>& w){
	checkexistsModSolver(modid);
	pModSolver m = getModSolver(modid);
	return m->addSet(setid, lits, w);
}

bool ModSolverData::addAggrExpr(modindex modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		throw idpexception();
	}
	checkexistsModSolver(modid);
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
	checkexistsModSolver(modid);
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
	checkexistsModSolver(modid);
	getModSolver(modid)->addAtoms(atoms);
}

bool ModSolverData::addChild(modindex parent, modindex child, Lit h){
	checkexistsModSolver(parent);
	if(existsModSolver(child)){
		reportf("Modal operator with id %d was already defined! ", child+1);
		throw idpexception();
	}
	if(sign(h)){
		reportf("Modal operator %d has a negative head. This is not allowed.", child+1);
		throw idpexception();
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
	return solvers[0]->solve();
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
			throw idpexception();
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
