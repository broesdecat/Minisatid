/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "theorysolvers/SOSolver.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

#include "modules/ModSolver.hpp"

#include <vector>

using namespace std;
using namespace MinisatID;

SOSolver::SOSolver(SolverOption modes, MinisatID::WLSImpl& inter)
		: LogicSolver(modes, inter), state(NEW){
	solvers.push_back(new ModSolver(0, -1, this));
	state = LOADINGHIER;
}

SOSolver::~SOSolver(){
	deleteList<ModSolver>(solvers);
}

void SOSolver::checkexistsModSolver(vsize modid) const {
	if(!existsModSolver(modid)){
		char s[100]; sprintf(s, ">> No modal operator with id %zu was declared! ", modid+1);
		throw idpexception(s);
	}
}

bool SOSolver::simplify(){
	assert(state==ALLLOADED);
	return solvers[0]->simplifyDown();
}

bool SOSolver::solve(const vec<Lit>& assumptions, const ModelExpandOptions& options){
	assert(state==ALLLOADED);
	return solvers[0]->solve(assumptions, options);
}

bool SOSolver::isRoot(const ModSolver* solver) const{
	return solvers[0]==solver;
}

void SOSolver::addModel(const InnerModel& model){
	getParent().addModel(model);
}

void SOSolver::finishParsing(bool& unsat){
	assert(state==LOADINGREST);
	state = ALLLOADED;

	verifyHierarchy();

//	if(!initialsolverone->solve()){
//		return false;
//	}
//	if(initialsolvertwo->solve()){
//		return true;
//	}

	solvers[0]->finishParsingDown(unsat);

	if(modes().verbosity>=2){
		print(this);
	}
}

bool SOSolver::add(int modid, const InnerSubTheory& subtheory){
	assert(state==LOADINGHIER);

	int child = subtheory.child;
	checkexistsModSolver(modid);
	if(sign(subtheory.head)){
		stringstream ss;
		ss <<">> Modal operator " <<child+1 <<" has a negative head.\n";
		throw idpexception(ss.str());
	}
	if(solvers.size()<child+1){
		solvers.resize(child+1, NULL);
	}
	Var head = var(subtheory.head);
	solvers[child] = new ModSolver(child, head, this);
	solvers[child]->setParent(modid);
	return true;
}
bool SOSolver::add(int modid, const InnerRigidAtoms& rigid){
	assert(state==LOADINGHIER);
	//allAtoms.insert(allAtoms.end(), atoms.begin(), atoms.end());
	checkexistsModSolver(modid);
	return getModSolver(modid)->add(rigid);
}

//Add information for PC-Solver

bool SOSolver::add(int modid, Var v){
	return getModSolverDuringAdding(modid).add(v);
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
bool SOSolver::add(int modid, const InnerDisjunction& disj){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);
/*
	//Check two initial propagation rules
	bool allexist = true;
	vec<Lit> onlyexists;
	for(int i=0; i<lits.size(); ++i){
		if(isForall(lits[i])){
			allexist = false;
		}else{
			onlyexists.push(lits[i]);
			//TODO forall reduction necessary!
		}
	}
	if(allexist){
		initialsolverone->addClause(lits);
	}
	initialsolvertwo->addClause(onlyexists);*/

	//Try to add a clause as high up in the hierarchy as possible.
	const vec<Lit>& lits = disj.literals;
	checkexistsModSolver(modid);
	vsize previd = modid, currentid = modid;
	ModSolver* m = NULL;
	bool negated = false;
	while(true){
		m = getModSolver(currentid);
		bool alloccur = true;
		for(int i=0; alloccur && i<lits.size(); ++i){
			bool seen = false;
			for(vector<Var>::const_iterator j=m->getAtoms().begin(); !seen && j<m->getAtoms().end(); ++j){
				if(*j==var(lits[i])){
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
	bool result;
	if(negated){
		result = getModSolver(previd)->add(disj);
	}else{
		result = getModSolver(currentid)->add(disj);
	}
	return result;
}

bool SOSolver::add(int modid, const InnerRule& rule){
	return getModSolverDuringAdding(modid).add(rule);
}
bool SOSolver::add(int modid, const InnerWSet& wset){
	return getModSolverDuringAdding(modid).add(wset);
}
bool SOSolver::add(int modid, const InnerAggregate& agg){
	return getModSolverDuringAdding(modid).add(agg);
}

ModSolver& SOSolver::getModSolverDuringAdding(int modid){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);

	checkexistsModSolver(modid);
	return *getModSolver(modid);
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
//TODO: should verify that any head only occurs in the theory of the parent modal solver.
void SOSolver::verifyHierarchy(){
	assert(state = ALLLOADED);

	vector<vsize> queue;
	vector<int> visitcount(solvers.size(), 0);
	queue.push_back(0);
	++visitcount[0];
	while(queue.size()>0){
		vsize s = queue.back();
		queue.pop_back();
		ModSolver* solver = getModSolver(s);
		for(vmodindex::const_iterator i=solver->getChildren().begin(); i<solver->getChildren().end(); ++i){
			if(visitcount[*i]==0){
				queue.push_back(*i);
			}
			++visitcount[*i];
		}
	}
	for(vmsolvers::const_iterator i=solvers.begin(); i<solvers.end(); ++i){
		if(visitcount[(*i)->getId()]!=1 && *i!=NULL){
			char s[200];
			sprintf(s, ">> The hierarchy of modal solvers does not form a tree. "
					"The Solver with id %zu is %s. \n",
						(*i)->getPrintId(),
						visitcount[(*i)->getId()]==0?"not referenced":"referenced multiple times");
			throw idpexception(s);
		}
	}
}
