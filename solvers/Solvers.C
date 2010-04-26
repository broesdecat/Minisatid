#include "Solvers.h"
#include "Utils.h"

void SolverData::addVar(Var v){
	while (v >= solver->nVars()) solver->newVar();
	solver->setDecisionVar(v,true); // S.nVars()-1   or   var
}

bool SolverData::addClause(vec<Lit>& lits){
	solver->addClause(lits);
	return false;
}
bool SolverData::addRule(bool conj, vec<Lit>& lits){
	idsolver->addRule(conj, lits);
	return false;
}
bool SolverData::addSet(int setid, vec<Lit>& lits, vector<Weight>& w){
	aggsolver->addSet(setid, lits, w);
	return false;
}

bool SolverData::addAggrExpr(Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		return true;
	}
	aggsolver->addAggrExpr(var(head), setid, bound, lower, type, defined);
	return false;
}

void SolverData::addMinimize(const vec<Lit>& lits, bool subsetmnmz){
	solver->addMinimize(lits, subsetmnmz);
}
void SolverData::addSumMinimize(const Var head, const int setid){
	solver->addSumMinimize(head, setid);
}


SolverData::SolverData():Data(){
	initializeSolvers(solver, idsolver, aggsolver);
}

void SolverData::setNbModels	(int nb)	{ solver->nb_models=nb; }
void SolverData::setRes			(FILE* f)	{ solver->res = f; }
bool SolverData::simplify		()			{ return solver->simplify(); }
bool SolverData::solve			()			{ return solver->solve(); }

void SolverData::finishParsing(){ //throws UNSAT
    //important to call definition solver last
	if(modes.aggr){
		modes.aggr = solver->getAggSolver()->finishECNF_DataStructures();
	}
	if(modes.def){
		modes.def = solver->getIDSolver()->finishECNF_DataStructures();
	}
	solver->finishParsing();

	if(!modes.aggr){
		solver->getAggSolver()->remove();
		if(modes.verbosity>0){
			reportf("|                                                                             |\n"
					"|    (there will be no aggregate propagations)                                |\n");
		}
	}
	if(!modes.def){
		solver->getIDSolver()->remove();
		if(modes.verbosity>0){
			reportf("|    (there will be no definitional propagations)                             |\n");
		}
	}
	if(!modes.mnmz){
		//later
	}
}

bool ModSolverData::addClause(modindex modid, vec<Lit>& lits){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	pModSolver m = getModSolver(modid);
	m->addClause(lits);
	return false;
}
bool ModSolverData::addRule(modindex modid, bool conj, vec<Lit>& lits){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	pModSolver m = getModSolver(modid);
	m->addRule(conj, lits);
	return false;
}
bool ModSolverData::addSet(modindex modid, int setid, vec<Lit>& lits, vector<Weight>& w){
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	pModSolver m = getModSolver(modid);
	m->addSet(setid, lits, w);
	return false;
}

bool ModSolverData::addAggrExpr(modindex modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		return true;
	}
	if(!existsModSolver(modid)){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	pModSolver m = getModSolver(modid);
	m->addAggrExpr(var(head), setid, bound, lower, type, defined);
	return false;
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
		return true;
	}
	for(vector<int>::const_iterator i=children.begin(); i<children.end(); i++){
		if(!existsModSolver(*i)){
			reportf("No modal operator with id %d was defined! ", *i+1);
			return true;
		}
	}
	pModSolver m = getModSolver(modid);
	m->setChildren(children);
	return false;
}

bool ModSolverData::simplify(){
	//FIXME
	return true;
}

bool ModSolverData::solve(){
	Clause* confl = solvers[0]->propagateDown(solvers[0]->getHead());
	if(confl!=NULL){
		return false;
	}

	solvers[0]->printModel();
	return true;
}

void ModSolverData::finishParsing(){
	solvers[0]->finishParsing();
}

void initializeSolvers(pSolver& s, pIDSolver& is, pAggSolver& as){
	s = shared_ptr<Solver>(new Solver());
	is = shared_ptr<IDSolver>(new IDSolver());
	as = shared_ptr<AggSolver>(new AggSolver());

	s->setIDSolver(is);
	s->setAggSolver(as);
	is->setSolver(s);
	is->setAggSolver(as);
	as->setSolver(s);
	as->setIDSolver(is);
}
