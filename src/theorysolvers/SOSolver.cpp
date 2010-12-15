//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#include "theorysolvers/SOSolver.hpp"
#include "utils/Utils.hpp"
#include "utils/Print.hpp"

#include "modules/ModSolver.hpp"

#include <vector>

using namespace std;
using namespace MinisatID;

SOSolver::SOSolver(SolverOption modes, MinisatID::WrappedLogicSolver* inter)
		: LogicSolver(modes, inter), state(NEW){
	solvers.push_back(new ModSolver(0, -1, this));
	state = LOADINGHIER;
}

SOSolver::~SOSolver(){
	deleteList<ModSolver>(solvers);
}

void SOSolver::checkexistsModSolver(vsize modid) const {
	if(!existsModSolver(modid)){
		char s[100]; sprintf(s, "No modal operator with id %zu was declared! ", modid+1);
		throw idpexception(s);
	}
}

bool SOSolver::simplify(){
	assert(state==ALLLOADED);
	return solvers[0]->simplifyDown();
}

bool SOSolver::solve(const vec<Lit>& assumptions, Solution* sol){
	assert(state==ALLLOADED);
	return solvers[0]->solve(assumptions, sol);
}

void SOSolver::finishParsing(bool& present, bool& unsat){
	assert(state==LOADINGREST);
	state = ALLLOADED;

	verifyHierarchy();

//	if(!initialsolverone->solve()){
//		return false;
//	}
//	if(initialsolvertwo->solve()){
//		return true;
//	}

	solvers[0]->finishParsingDown(present, unsat);

	if(modes().verbosity>=2){
		Print::print(this);
	}
}

//Add information for hierarchy

bool SOSolver::addChild(vsize parent, vsize child, Lit h){
	assert(state==LOADINGHIER);

	checkexistsModSolver(parent);
	if(existsModSolver(child)){
		char s[100]; sprintf(s, "Modal operator with id %zu was already defined!\n", child+1);
		throw idpexception(s);
	}
	if(sign(h)){
		char s[100]; sprintf(s, "Modal operator %zu has a negative head.\n", child+1);
		throw idpexception(s);
	}
	if(solvers.size()<child+1){
		solvers.resize(child+1, NULL);
	}
	Var head = var(h);
	solvers[child] = new ModSolver(child, head, this);
	solvers[child]->setParent(parent);
	return true;
}

bool SOSolver::addAtoms(vsize modid, const vector<Var>& atoms){
	assert(state==LOADINGHIER);

	//allAtoms.insert(allAtoms.end(), atoms.begin(), atoms.end());

	checkexistsModSolver(modid);
	return getModSolver(modid)->addAtoms(atoms);
}

//Add information for PC-Solver

void SOSolver::addVar(vsize modid, Var v){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);

	//allAtoms.push_back(v);

	checkexistsModSolver(modid);
	getModSolver(modid)->addVar(v);
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
bool SOSolver::addClause(vsize modid, vec<Lit>& lits){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);
/*
	//Check two initial propagation rules
	bool allexist = true;
	vec<Lit> onlyexists;
	for(int i=0; i<lits.size(); i++){
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
	checkexistsModSolver(modid);
	vsize previd = modid, currentid = modid;
	ModSolver* m = NULL;
	bool negated = false;
	while(true){
		m = getModSolver(currentid);
		bool alloccur = true;
		for(int i=0; alloccur && i<lits.size(); i++){
			bool seen = false;
			for(vector<Var>::const_iterator j=m->getAtoms().begin(); !seen && j<m->getAtoms().end(); j++){
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
		//reportf("orig %d => new %d\n", modid, previd);
		result = getModSolver(previd)->addClause(lits);
	}else{
		//reportf("orig %d => new %d\n", modid, currentid);
		result = getModSolver(currentid)->addClause(lits);
	}
	return result;
}

bool SOSolver::addRule(vsize modid, bool conj, Lit head, vec<Lit>& lits){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);

	checkexistsModSolver(modid);
	ModSolver* m = getModSolver(modid);
	return m->addRule(conj, head, lits);
}

bool SOSolver::addSet(vsize modid, int setid, vec<Lit>& lits, vector<Weight>& w){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);

	checkexistsModSolver(modid);
	ModSolver* m = getModSolver(modid);
	return m->addSet(setid, lits, w);
}

bool SOSolver::addAggrExpr(vsize modid, Lit head, int setid, const Weight& bound, AggSign boundsign, AggType type, AggSem defined){
	if(state==LOADINGHIER){
		state = LOADINGREST;
	}
	assert(state==LOADINGREST);

	if(sign(head)){
		throw idpexception("Negative heads are not allowed for aggregate expressions!\n");
	}
	checkexistsModSolver(modid);
	ModSolver* m = getModSolver(modid);
	return m->addAggrExpr(head, setid, bound, boundsign, type, defined);
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
	visitcount[0]++;
	while(queue.size()>0){
		vsize s = queue.back();
		queue.pop_back();
		ModSolver* solver = getModSolver(s);
		for(vmodindex::const_iterator i=solver->getChildren().begin(); i<solver->getChildren().end(); i++){
			if(visitcount[*i]==0){
				queue.push_back(*i);
			}
			visitcount[*i]++;
		}
	}
	for(vmsolvers::const_iterator i=solvers.begin(); i<solvers.end(); i++){
		if(visitcount[(*i)->getId()]!=1 && *i!=NULL){
			char s[200];
			sprintf(s, "The hierarchy of modal solvers does not form a tree. "
					"The Solver with id %zu is %s. \n",
						(*i)->getPrintId(),
						visitcount[(*i)->getId()]==0?"not referenced":"referenced multiple times");
			throw idpexception(s);
		}
	}
}
