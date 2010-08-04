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

#include <set>
#include <map>

#include "solvers/cpsolver/CPSolver.hpp"
#include "solvers/cpsolver/CPScript.hpp"

#include "solvers/cpsolver/CPUtils.hpp"
#include "solvers/pcsolver/PCSolver.hpp"

#include <solvers/cpsolver/Constraint.hpp>
#include <solvers/cpsolver/CPSolverData.hpp>

using namespace std;

namespace CP {
	class CPScript;
	class CPSolverData;
}

using namespace CP;

CPSolver::CPSolver(PCSolver * solver): ISolver(solver), solverdata(new CPSolverData()) {

}

CPSolver::~CPSolver() {
	delete solverdata;
}

/////////////////////////////////////////
//	INITIALIZATION
/////////////////////////////////////////

// FIXME: some simplifications/propagations are done immediately when adding a constraint to the constraint store
// these can/should be propagated as soon as possible

// FIXME: reification atoms have to be unique! CHECK THIS

void CPSolver::addTerm(int term, int min, int max){
	assert(!isInitialized());
	getSolverData()->addTerm(TermIntVar(getSolverData()->getSpace(), term, min, max));
}

bool CPSolver::addBinRel(int groundname, MINISAT::EqType rel, int bound, int atom){
	assert(!isInitialized());
	TermIntVar lhs(solverdata->convertToVar(groundname));

	if(getPCSolver()->modes().verbosity>=10){
		cout <<"Added binary relation " <<gprintVar(atom) <<" <=> " <<lhs <<" " <<rel <<" "<<bound <<endl;
	}

	getSolverData()->addReifConstraint(new BinArithConstraint(getSolverData()->getSpace(), lhs, toRelType(rel), bound, atom));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addBinRelVar(int groundname, MINISAT::EqType rel, int groundname2, int atom){
	assert(!isInitialized());
	TermIntVar lhs(getSolverData()->convertToVar(groundname));
	TermIntVar rhs(getSolverData()->convertToVar(groundname2));

	if(getPCSolver()->modes().verbosity>=10){
		cout <<"Added binary relation " <<gprintVar(atom) <<" <=> " <<lhs <<" " <<rel <<" "<<rhs <<endl;
	}

	getSolverData()->addReifConstraint(new BinArithConstraint(getSolverData()->getSpace(), lhs, toRelType(rel), rhs, atom));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addSum(vector<int> term, MINISAT::EqType rel, int bound, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, toRelType(rel), bound, atom));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addSum(vector<int> term, vector<int> mult, MINISAT::EqType rel, int bound, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, mult, toRelType(rel), bound, atom));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addSumVar(vector<int> term, MINISAT::EqType rel, int rhsterm, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	TermIntVar rhs(getSolverData()->convertToVar(rhsterm));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, toRelType(rel), rhs, atom));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addSumVar(vector<int> term, vector<int> mult, MINISAT::EqType rel, int rhsterm, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	TermIntVar rhs(getSolverData()->convertToVar(rhsterm));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, mult, toRelType(rel), rhs, atom));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addCount(vector<int> terms, MINISAT::EqType rel, int value, int rhsterm){
	assert(!isInitialized());

	if(getPCSolver()->modes().verbosity>=10){
		cout <<"Added Count(";
		for(vector<int>::const_iterator i=terms.begin(); i<terms.end(); i++){
			cout << *i <<"=" <<value <<", ";
		}
		cout <<") " <<rel << " " <<rhsterm <<endl;
	}

	vector<TermIntVar> set(getSolverData()->convertToVars(terms));
	TermIntVar rhs(getSolverData()->convertToVar(rhsterm));
	getSolverData()->addNonReifConstraint(new CountConstraint(getSolverData()->getSpace(), set, toRelType(rel), value, rhs));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

bool CPSolver::addAllDifferent(vector<int> term){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	getSolverData()->addNonReifConstraint(new DistinctConstraint(getSolverData()->getSpace(), set));

	StatusStatistics stats;
	return getSolverData()->getSpace().status(stats) != SS_FAILED;
}

////////////////////////////
//	SOLVER METHODS
////////////////////////////

// Space management:
//		First space = space after adding all constraints and propagating until fixpoint
//		Any subsequent space is after adding ALL propagations of a decision level and propagating until fixpoint
//			so this can be MULTIPLE fixpoint propagations until next decision level!

rClause CPSolver::getExplanation(const Lit& p){
	vec<Lit> lits;
	bool found = false;
	lits.push(p);
	for(vector<Lit>::const_iterator i=trail.begin(); !found && i<trail.end(); i++){
		if(var(*i)==var(p)){
			found = true;
		}else{
			lits.push(~(*i));
		}
	}
	assert(found);
	rClause c = getPCSolver()->addLearnedClause(lits);
	return c;
}

rClause CPSolver::notifySATsolverOfPropagation(const Lit& p) {
	if (getPCSolver()->value(p) == l_False) {
		if (getPCSolver()->modes().verbosity >= 2) {
			reportf("Deriving conflict in "); gprintLit(p, l_True);
			reportf(" because of the constraint TODO \n");
		}
		rClause confl = getExplanation(p);
		return confl;
	} else if (getPCSolver()->value(p) == l_Undef) {
		if (getPCSolver()->modes().verbosity >= 2) {
			reportf("Deriving "); gprintLit(p, l_True);
			reportf(" because of the constraint expression TODO \n");
		}
		getPCSolver()->setTrue(p);
	} else {
	}
	return nullPtrClause;
}

bool CPSolver::finishParsing(){
	assert(!isInitialized());
	notifyInitialized();

	// Propagate until fixpoint
	StatusStatistics stats;
	SpaceStatus status = getSolverData()->getSpace().status(stats);

	if(status==SS_FAILED){
		return false;
	}

	// Propagate all assigned reification atoms. If any conflicts, return false
	for(vector<ReifiedConstraint*>::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
		if((*i)->isAssigned(getSolverData()->getSpace())){

		}
		rClause confl = notifySATsolverOfPropagation(mkLit((*i)->getAtom(), (*i)->isAssignedFalse(getSolverData()->getSpace())));
		if(confl!=nullPtrClause){
			return false;
		}
	}

	//Add a new timepoint to the history
	getSolverData()->addSpace();

	return true;
}

rClause CPSolver::propagate(Lit l){
	rClause confl = nullPtrClause;
	if (isInitialized()) {return confl;}

	for(vreifconstrptr::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
		if((*i)->getAtom()==var(l)){
			if(getPCSolver()->modes().verbosity >= 5){
				reportf("Propagated into CP: "); gprintLit(l); reportf(".\n");
			}
			trail.push_back(l);
			return (*i)->propagate(!sign(l), getSolverData()->getSpace());
		}
	}
	return confl;
}

/**
 * Backtrack one decision level
 */
void CPSolver::backtrack(){
	if(isInitialized()){ return; }
	getSolverData()->backtrack();
}

/**
 * Backtrack one literal
 */
void CPSolver::backtrack(Lit l){ //TODO only useful for trail
	if(trail.size()>0 && l==trail.back()){
		trail.pop_back();
	}
}

rClause CPSolver::propagateAtEndOfQueue(){
	rClause confl = nullPtrClause;
	if (isInitialized()) { return confl; }

	StatusStatistics stats;
	SpaceStatus status = solverdata->getSpace().status(stats);

	if(status == SS_FAILED){
		//Conflict
		//Very simple clause generation:
		vec<Lit> clause;
		//FIXME should be of PREVIOUS space!
		//FIXME ADD STACK IN CORRECT ORDER! First add the conflicting one!
		for(vector<ReifiedConstraint*>::const_iterator i=solverdata->getReifConstraints().begin(); i<solverdata->getReifConstraints().end(); i++){
			if(isTrue((*i)->getBoolVar(solverdata->getSpace()))){
				clause.push(mkLit((*i)->getAtom(), true));
			}else if(isFalse((*i)->getBoolVar(solverdata->getSpace()))){
				clause.push(mkLit((*i)->getAtom()));
			}
		}
		for(int i=0; i<trail.size(); i++){
			clause.push(~trail[i]);
		}

		confl = getPCSolver()->addLearnedClause(clause);
	}else{
		if(solverdata->allBooleansKnown()){
			confl = propagateFinal();
		}

		// If no conflict, propagate all changes
		if(confl==nullPtrClause){
			vector<Lit> atoms = solverdata->getBoolChanges();
			for(vector<Lit>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
				notifySATsolverOfPropagation(*i);
			}
			solverdata->addSpace();
		}
	}

	return confl;
}

rClause CPSolver::propagateFinal(){
	rClause confl = nullPtrClause;

	Search::Options searchOptions_;
	DFS<CPScript>* searchEngine_; // depth first search
	CPScript* enumerator_ = NULL;

	solverdata->getSpace().addBranchers();

	searchOptions_ = Search::Options::def;
	searchOptions_.stop = NULL; //new Search::MemoryStop(1000000000);

	searchEngine_ = new DFS<CPScript>(&solverdata->getSpace(), searchOptions_);
	enumerator_ = searchEngine_->next();

	if(enumerator_==NULL){
		if(searchEngine_->stopped()){
			throw idpexception("memory overflow on CP part");
		}else{
			cout <<"Conflict found" <<endl;
			assert(false);
			//TODO add conflict clause
		}
	}else{
		//FIXME: adding this as a space brings problems, because on backtracking two space have to be removed instead of one
		//on the other hand, not adding it would not be consistent, as the last space has to be the one with the real solution!
		//maybe replacing might help?
		solverdata->addSpace(enumerator_);
		/*for(int i=0; i<solverdata->size(); i++){
			cout << *solverdata->operator[](i) <<endl;
		}*/
		cout <<*enumerator_<<endl;
	}

	return confl;
}

//Space* space = new CPScript();
//history.push_back(space);
//
//SizeOptions opt("Test configuration");
//opt.icl(ICL_DOM);
//opt.size(18);
//
//int periods = 10;
//IntVarArgs n(periods);
//IntVar n2;
//
//for (int p=0; p<periods; p++){
//	n[p].init(*space,1,10);
//}
//
//distinct(*space, n, opt.icl());
//
//StatusStatistics* s = new StatusStatistics();
//SpaceStatus status = space->status(*s);
//if(status==SS_FAILED){
//	reportf("No solution\n");
//}else if(status==SS_SOLVED){
//	reportf("Solution found\n");
//}else{
//	reportf("Choices left to make\n");
//}
//
//Gecode::Int::IntView x;
//x.lq(*space, 5);

///**
// * The new propagator that will be registered to all boolean change events
// */
//class DPLLTPropagator: public Propagator{
//protected:
//  /// Constructor for posting
//	DPLLTPropagator(Home home, ViewArray<View>& x): Propagator(home){
//
//	}
//  /// Constructor for cloning \a p
//	DPLLTPropagator(Space& home, bool share, DPLLTPropagator& p): Propagator(home){
//
//	}
//public:
//  /// Copy propagator during cloning
//  virtual Actor*     copy(Space& home, bool share){
//
//  }
//  /// Perform propagation
//  virtual ExecStatus propagate(Space& home, const ModEventDelta& med){
//
//  }
//  /// Post propagator for view array \a x
//  static ExecStatus post(Home home, ViewArray<BoolView>& x){
//	  new (home) Val<View>(home,x);
//	  return ES_OK;
//  }
//};
//
//void
//dpllprop(Home home, const BoolVarArgs& x) {
//	if (home.failed()) return;
//	ViewArray<BoolView> xv(home,x);
//	GECODE_ES_FAIL(DPLLTPropagator::post(home,xv));
//}
