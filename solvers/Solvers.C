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

bool ModSolverData::addClause(int modid, vec<Lit>& lits){
	pModSolver m = getModSolver(modid);
	if(m==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	m->addClause(lits);
	return false;
}
bool ModSolverData::addRule(int modid, bool conj, vec<Lit>& lits){
	pModSolver m = getModSolver(modid);
	if(m==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	m->addRule(conj, lits);
	return false;
}
bool ModSolverData::addSet(int modid, int setid, vec<Lit>& lits, vector<Weight>& w){
	pModSolver m = getModSolver(modid);
	if(m==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	m->addSet(setid, lits, w);
	return false;
}

bool ModSolverData::addAggrExpr(int modid, Lit head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	if(sign(head)){
		reportf( "No negative heads are allowed!\n");
		return true;
	}
	pModSolver m = getModSolver(modid);
	if(m==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	m->addAggrExpr(var(head), setid, bound, lower, type, defined);
	return false;
}

SolverData::SolverData():Data(){
	initializeSolvers(solver, idsolver, aggsolver);
}

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

void ModSolverData::addVar(Var v){
	for(vector<pModSolver>::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		(*i)->addVar(v);
	}
}

ModSolverData::ModSolverData():Data(){}

ModSolverData::~ModSolverData(){
	deleteList<ModSolver>(solvers);
}

void ModSolverData::initialize(){
	vector<int> l;
	solvers.push_back(new ModSolver(false, 0, -1, l, shared_from_this()));
}

bool ModSolverData::addModSolver(int modid, Var head, bool neg, const vector<Var>& atoms){
	assert(modid>0);
	if(solvers.size()<modid+1){
		solvers.resize(modid+1, NULL);
	}
	assert(solvers[modid]==NULL);
	solvers[modid] = new ModSolver(neg, modid, head, atoms, shared_from_this());
	return false;
}

bool ModSolverData::addChildren(int modid, const vector<int>& children){
	pModSolver m = getModSolver(modid);
	if(m==NULL){
		reportf("No modal operator with id %d was defined! ", modid+1);
		return true;
	}
	for(vector<int>::const_iterator i=children.begin(); i<children.end(); i++){
		if(getModSolver(*i)==NULL){
			reportf("No modal operator with id %d was defined! ", *i+1);
			return true;
		}
	}
	m->setChildren(children);
	return false;
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
