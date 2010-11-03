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

#include "solvers/modules/ModSolver.hpp"

#include "solvers/utils/Utils.hpp"
#include "solvers/utils/Print.hpp"
#include <vector>
#include <algorithm>

#include "solvers/external/ExternalInterface.hpp"
#include "solvers/theorysolvers/PCSolver.hpp"
#include "solvers/theorysolvers/SOSolver.hpp"

using namespace std;
using namespace MinisatID;

//Important: The head variable does not occur in this theory, so should NOT automatically be
//added as a var in it.
/**
 * Constructs a ModSolver, with a given head, index and hierarchy pointer. A PCSolver is initialized.
 */
ModSolver::ModSolver(modindex child, Var head, SOSolver* mh):
		DPLLTmodule(NULL),
		id(child), parentid(-1), hasparent(false), //, startedsearch(false), startindex(-1),
		head(head), modhier(mh){
	ECNF_mode modescopy(mh->modes());
	modescopy.nbmodels = 1;

	pcsolver = new PCSolver(modescopy, mh->getParent());
	getPCSolver()->setModSolver(this);
}

ModSolver::~ModSolver(){
	delete solver;
}

/******************************
 * ADD/INITIALIZATION METHODS *
 ******************************/

void ModSolver::addVar(Var var){
	if(getModSolverData().modes().verbosity>5){
		report("Var %d added to modal solver %zu.\n", var, getPrintId());
	}
	getPCSolver()->addVar(var);
}

/**
 * Add all variables in the given vector as variables in the theory.
 */
void ModSolver::addVars(vec<Lit>& a){
	for(int i=0; i<a.size(); i++){
		addVar(var(a[i]));
	}
}

bool ModSolver::addClause(vec<Lit>& lits){
	addVars(lits);
	return getPCSolver()->addClause(lits);
}

bool ModSolver::addRule(bool conj, Lit head, vec<Lit>& lits){
	addVar(head);
	addVars(lits);
	return getPCSolver()->addRule(conj, head, lits);
}

bool ModSolver::addSet(int setid, vec<Lit>& lits, vector<Weight>& w){
	addVars(lits);
	return getPCSolver()->addSet(setid, lits, w);
}

bool ModSolver::addAggrExpr(Lit head, int set_id, Weight bound, AggSign boundsign, AggType type, AggSem defined){
	addVar(var(head));
	return getPCSolver()->addAggrExpr(head, set_id, bound, boundsign, type, defined);
}

/**
 * Adds the list of variables to the rigid atoms of this ModSolver. They are automatically added
 * as variables, this is maybe not completely necessary when they are not used in the PC theory,
 * but requires some algorithmic changes then, so currently they are added. In addition,
 * they are added as variables to the parent solver, that has to decide on values for them.
 */
bool ModSolver::addAtoms(const vector<Var>& a){
	for(vector<Var>::const_iterator i=a.begin(); i<a.end(); i++){
		atoms.push_back(*i);
		addVar(*i);
		getModSolverData().getModSolver(getParentId())->addVar(*i);
	}

	//Creates a bool-vector mapping each atom to whether it was propagated from above or from this theory
	propfromabove = vector<bool>(atoms.size(), false);

	return true;
}


/**
 * Sets the id of the parent modal solver. All rigid atoms are then added (possibly again) to the
 * parent solver, as well as this solver as a child and the head as a variable.
 */
void ModSolver::setParent(modindex id){
	parentid = id; hasparent = true;
	pModSolver parent = getModSolverData().getModSolver(getParentId());
	for(vector<Var>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		parent->addVar(*i);
	}
	parent->addChild(this->id);
	parent->addVar(head.atom);
}

/**
 * Adds a modal solver as a child of this solver, by id.
 */
void ModSolver::addChild(modindex childid){
	children.push_back(childid);
}

/**
 * Recursively notify all Solvers that parsing has finished
 */
void ModSolver::finishParsingDown(bool& present, bool& unsat){
	getPCSolver()->finishParsing(present, unsat);

	assert(present);

	for(vmodindex::const_iterator i=getChildren().begin(); !unsat && i<getChildren().end(); i++){
		bool childpresent = true;
		getModSolverData().getModSolver(*i)->finishParsingDown(childpresent, unsat);
		//TODO handle !present
		//TODO handle unsat => might make this solver !present
	}

	notifyInitialized();
}

/*****************
 * SOLVE METHODS *
 *****************/

/**
 * Tells the root solver to do model expansion on his theory
 */
bool ModSolver::solve(const vec<Lit>& assumptions, Solution* sol){
	return getPCSolver()->solve(assumptions, sol);
}

/*
 * Simplifies PC solver and afterwards simplifies lower modal operators.
 * Returns false if the problem is unsat (and then does not simplify other solvers).
 */
bool ModSolver::simplifyDown(){
	bool result = getPCSolver()->simplify();

	for(vmodindex::const_iterator i=getChildren().begin(); result && i<getChildren().end(); i++){
		result = getModSolverData().getModSolver(*i)->simplify();
		//TODO check if this is correct: i think it is not guaranteed that all lower solvers will be searched!
		//It is anyway necessary, because if no search occurs, the modal solvers should still be checked!
		//TODO can this be called multiple times (it shouldn't)
		if(result){
			vec<Lit> confl;
			if(!getModSolverData().getModSolver(*i)->propagateDownAtEndOfQueue(confl)){
				result = false;
			}
		}
	}

	return result;
}

/**
 * Propagates l to be true from the parent modal solver.
 * As long as the PC-solver is still propagating, this solver should not do anything more than store
 * the propagation, as modal satisfiability checking can be much more expensive. So this solver always
 * return NULL (if not, it should return a non-owning pointer).
 */
rClause ModSolver::propagateDown(Lit l){
	if(getModSolverData().modes().verbosity>4){
		gprintLit(l); report(" propagated down into modal solver %zu.\n", getPrintId());
	}

	adaptValuesOnPropagation(l);

	return nullPtrClause;
}

/**
 * Checks whether l is relevant to this modal theory (the head or a rigid atom).
 * If this is the case, it adapts the data structures.
 */
void ModSolver::adaptValuesOnPropagation(Lit l){
	//Adapt head value
	if(getHead()==var(l)){
		assert(getHeadValue()==l_Undef);
		head.value = !sign(l)?l_True:l_False;
	}

	//adapt rigid atoms value
	for(vector<AV>::size_type i=0; i<atoms.size(); i++){
		if(var(l)==atoms[i]){
			propfromabove[i]=true;
			assumptions.push(l);
			break;
		}
	}
}

/**
 * Notifies the modal solver that propagation of the parent solver are finished. At this point, the modal solver
 * will be propagated.
 * Returns true if no conflict ensues
 */
bool ModSolver::propagateDownAtEndOfQueue(vec<Lit>& confldisj){
	if(!isInitialized()){ return true; }
	if(getModSolverData().modes().verbosity>4){
		report("End of queue propagation down into modal solver %zu.\n", getPrintId());
	}

	bool allknown = false;

	/*TODO future:
	bool result;
	if(!allknown){
		result = doUnitPropagation(assumpts);
	}else{
		result = search(assumpts);
	}
	*/

	if(assumptions.size()==getAtoms().size() && (!hasparent || getHeadValue()!=l_Undef)){
		allknown = true;
	}

	bool result = search(assumptions, allknown);

	result = analyzeResult(result, allknown, confldisj);

	if(getModSolverData().modes().verbosity>4){
		report("Finished checking solver %zu: %s.\n", getPrintId(), result?"no conflict":"conflict");
	}

	getPCSolver()->backtrackTo(0);

	return result;
}

void ModSolver::doUnitPropagation(const vec<Lit>& assumpts){

}

bool ModSolver::search(const vec<Lit>& assumpts, bool search){
	/*
	 * In the end, we would want to propagate level by level, without having to restart the whole process
	 * every time. This requires a startsearch and continuesearch procedure in the SAT-solver
	 * As this is rather tedious, we will delay it until necessary.
	bool result = true;
	if(startindex==-1){
		result = getPCSolver()->startSearch();
		startindex = 0;
	}
	for(; result && startindex<assumptions.size(); startindex++){
		result = getPCSolver()->propagate(assumptions[startindex]);
	}
	if(search && result){
		searching = true;
		result = getPCSolver()->continueSearch();
		searching = false;
	}

	return result;*/

	bool result;
	searching = search;
	Solution* sol = new Solution(false, false, searching, 1, vector<Literal>());
	result = getPCSolver()->solve(assumpts, sol);
	delete sol;
	searching = false;
	return result;
}

/**
 * Important, returns a clause constructed to be added to the PARENT solver: the vars are NOT necessarily
 * decision vars in this PC solver
 * Returns true if no conflict ensues
 */
bool ModSolver::analyzeResult(bool result, bool allknown, vec<Lit>& confldisj){
	bool conflict = false;
	//if no model found and should be sat or if model found, should be unsat and all values are known
	if(getHeadValue()==l_True && !result){
		conflict = true;
	}
	if(getHeadValue()==l_False && result && allknown){
		conflict = true;
	}

	if(conflict){ //conflict between head and body
		//TODO can the clause learning be improved?
		assert(confldisj.size()==0);
		if(getHeadValue()!=l_Undef){
			confldisj.push(mkLit(getHead(), getHeadValue()==l_True));
		}
		//TODO order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for(int i=0; i<assumptions.size(); i++){
			if(propfromabove[i]){
				confldisj.push(~assumptions[i]);
			}
		}
		assert(confldisj.size()>0);
	}

	return !confldisj;
}

/**
 * Returns non-owning pointer
 */
rClause ModSolver::propagate(const Lit& l){
	/*if(!searching){
		vector<Lit> v = getPCSolver()->getDecisions();
		//TODO propagate up WITH reason
	}*/
	rClause confl = nullPtrClause;
	for(vmodindex::const_iterator i=getChildren().begin(); confl==nullPtrClause && i<getChildren().end(); i++){
		confl = getModSolverData().getModSolver(*i)->propagateDown(l);
	}
	return confl;
}

//In future, we might want to delay effectively propagating and searching in subfolders to the point where the
//queue is empty, so we will need a propagateDown and a propagateDownEndOfQueue
/**
 * Returns non-owning pointer
 */
rClause ModSolver::propagateAtEndOfQueue(){
	bool noconflict = true;
	vec<Lit> confldisj;
	for(vmodindex::const_iterator i=getChildren().begin(); noconflict && i<getChildren().end(); i++){
		assert(confldisj.size()==0);
		noconflict = getModSolverData().getModSolver(*i)->propagateDownAtEndOfQueue(confldisj);
	}

	rClause confl = nullPtrClause;
	if(!noconflict){
		confl = getPCSolver()->createClause(confldisj, true);
		getPCSolver()->addLearnedClause(confl);

		if(getModSolverData().modes().verbosity>=5){
			Print::printClause(confl, getPCSolver());
		}
	}
	return confl;
}

void ModSolver::propagateUp(Lit l, modindex id){
	assert(false);
	//TODO
	//include reason or extend getexplanation to modal solvers (first is maybe best)
	//save id for clause learning
	getPCSolver()->setTrue(l, this);
}

/**
 * For backtracking on rigid atoms, there are two possibilities:
 * 		the backtracking comes from above, so it has to be done
 * 		the backtracking is from the PC-solver
 * 			in this case, it might be that it was propagated or chosen by the PC Solver, in which case it should be backtracked
 * 						or it might be that it was propagated from above, in which case it should NOT be backtracked
 * 			currently, this is solved by storing an boolean remembering whether it was propagated from above or from the pc solver
 */
void ModSolver::backtrackFromAbove(Lit l){
	if(getModSolverData().modes().verbosity>4){
		report("Backtracking "); gprintLit(l); report(" from above in mod %zu\n", getPrintId());
	}

	if(var(l)==getHead() && getHeadValue()!=l_Undef){
		head.value = l_Undef;
	}
	for(vector<AV>::size_type i=0; i<atoms.size(); i++){
		if(atoms[i]==var(l)){
			if(propfromabove[i] && var(l)==var(assumptions.last())){
				assumptions.pop();
				//startindex--;
				int solverlevel = getPCSolver()->getLevel(var(l));
				if(solverlevel>=0){ //otherwise it was not propagated!
					getPCSolver()->backtrackTo(solverlevel);
				}
				propfromabove[i] = false;
				break;
			}else{
#ifndef NDEBUG
				for(int j=0; j<assumptions.size(); j++){
					assert(var(assumptions[j])!=var(l));
				}
#endif
			}
		}
	}
}

/*void ModSolver::backtrack(const Lit& l){
	//FIXME FIXME Should be implemented otherwise
	if(getModSolverData().modes().verbosity>4){
		report("Backtracking "); gprintLit(l); report(" from same level in mod %zu\n", getPrintId());
	}

	//for(vector<AV>::size_type i=0; i<atoms.size(); i++){
	//	if(atoms[i].atom==var(l)){
	//		assert(false);
	//	}
	//}

	for(vmodindex::const_iterator j=getChildren().begin(); j<getChildren().end(); j++){
		getModSolverData().getModSolver((*j))->backtrackFromAbove(l);
	}
}*/

void ModSolver::print(){
	Print::print(this);
}

void ModSolver::printModel(){
	//TODO implement
	throw idpexception("Not yet implemented");
	//getPCSolver()->printModel();
}
