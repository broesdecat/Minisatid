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
#include "solvers/utils/Print.hpp"

using namespace std;

namespace CP {
	class CPScript;
	class CPSolverData;
}

using namespace CP;

CPSolver::CPSolver(PCSolver * solver): ISolver(solver), solverdata(new CPSolverData()),
		endenqueus(0){

}

CPSolver::~CPSolver() {
	delete solverdata;
}

/////////////////////////////////////////
//	INITIALIZATION
/////////////////////////////////////////

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

	return true;
}

bool CPSolver::addBinRelVar(int groundname, MINISAT::EqType rel, int groundname2, int atom){
	assert(!isInitialized());
	TermIntVar lhs(getSolverData()->convertToVar(groundname));
	TermIntVar rhs(getSolverData()->convertToVar(groundname2));

	if(getPCSolver()->modes().verbosity>=10){
		cout <<"Added binary relation " <<gprintVar(atom) <<" <=> " <<lhs <<" " <<rel <<" "<<rhs <<endl;
	}

	getSolverData()->addReifConstraint(new BinArithConstraint(getSolverData()->getSpace(), lhs, toRelType(rel), rhs, atom));

	return true;
}

bool CPSolver::addSum(vector<int> term, MINISAT::EqType rel, int bound, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, toRelType(rel), bound, atom));

	return true;
}

bool CPSolver::addSum(vector<int> term, vector<int> mult, MINISAT::EqType rel, int bound, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, mult, toRelType(rel), bound, atom));

	return true;
}

bool CPSolver::addSumVar(vector<int> term, MINISAT::EqType rel, int rhsterm, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	TermIntVar rhs(getSolverData()->convertToVar(rhsterm));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, toRelType(rel), rhs, atom));

	return true;
}

bool CPSolver::addSumVar(vector<int> term, vector<int> mult, MINISAT::EqType rel, int rhsterm, int atom){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	TermIntVar rhs(getSolverData()->convertToVar(rhsterm));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, mult, toRelType(rel), rhs, atom));

	return true;
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

	return true;
}

bool CPSolver::addAllDifferent(vector<int> term){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(term));
	getSolverData()->addNonReifConstraint(new DistinctConstraint(getSolverData()->getSpace(), set));

	return true;
}

////////////////////////////
//	SOLVER METHODS
////////////////////////////

// Space management:
//		First space = space after adding all constraints and propagating until fixpoint
//		Any subsequent space is after adding ALL propagations of a decision level and propagating until fixpoint
//			so this can be MULTIPLE fixpoint propagations until next decision level!

rClause CPSolver::getExplanation(const Lit& p){
	// Important: reason is necessary, because a literal might be derived by CP, but
	// requested an explanation before it is effectively propagated and in the trail itself

	assert(propreason[p]!=-1);

	vec<Lit> lits;
	lits.push(p);
	for(vector<Lit>::size_type i=0; i<propreason[p]; i++){
		if(propagations.find(var(trail[i])) == propagations.end()){
			lits.push(~trail[i]);
		}
	}
	rClause c = getPCSolver()->addLearnedClause(lits);
	return c;
}

rClause CPSolver::notifySATsolverOfPropagation(const Lit& p) {
	if (getPCSolver()->value(p) == l_False) {
		if (getPCSolver()->modes().verbosity >= 2) {
			reportf("Deriving conflict in "); gprintLit(p, l_True);
			reportf(" because of the constraint TODO \n");
		}
		vector<Lit>::size_type temp = propreason[p];
		propreason[p] = trail.size();
		rClause confl = getExplanation(p);
		propreason[p] = temp;
		return confl;
	} else if (getPCSolver()->value(p) == l_Undef) {
		if (getPCSolver()->modes().verbosity >= 2) {
			reportf("Deriving "); gprintLit(p, l_True);
			reportf(" because of the constraint expression TODO \n");
		}
		propreason[p] = trail.size();
		propagations.insert(var(p));
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
			rClause confl = notifySATsolverOfPropagation(mkLit((*i)->getAtom(), (*i)->isAssignedFalse(getSolverData()->getSpace())));
			if(confl!=nullPtrClause){
				return false;
			}
		}
	}

	return true;
}

//TODO clarify use here of backtrack methods

void CPSolver::newDecisionLevel(){
	//Add a new timepoint to the history
	getSolverData()->addSpace();
}

void CPSolver::backtrackDecisionLevel(){
	if(!isInitialized()){ return; }
	getSolverData()->removeSpace();
}

rClause CPSolver::propagate(Lit l){
	rClause confl = nullPtrClause;
	if (!isInitialized()) { return confl; }

#ifdef DEBUG
	for(int i=0; i<trail.size(); i++){
		assert(var(trail[i])!=var(l));
	}
#endif

	for(vreifconstrptr::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
		if((*i)->getAtom()==var(l)){
			if(getPCSolver()->modes().verbosity >= 5){
				reportf("Propagated into CP: "); gprintLit(l); reportf(".\n");
			}
			trail.push_back(l);
			if((*i)->isAssigned(getSolverData()->getSpace())){
				return confl;
			}
			return (*i)->propagate(!sign(l), getSolverData()->getSpace());
		}
	}
	return confl;
}

void CPSolver::backtrack(Lit l){
	if(trail.size()>0 && l==trail.back()){
		trail.pop_back();
		propagations.erase(var(l));
	}

	propreason[l] = -1;
}

/**
 * Very simple clause generation: use all literals that were propagated into the CP solver
 * 		(and which represent reification atoms)
 */
rClause CPSolver::genFullConflictClause(){
	// TEMPORARY CODE: find conflicting propagated literal => start from previous space
	/*reportf("Finding shortest reason \n");
	CPScript& space = *static_cast<CPScript*>(getSolverData()->getPrevSpace().clone());
	space.addBranchers();
	vector<Lit>::const_iterator nonassigned = trail.begin();
	int currentlevel = getPCSolver()->getLevel(var(trail.back()));
	reportf("Current level: %d\n", currentlevel);
	for(; nonassigned<trail.end(); nonassigned++){
		if(getPCSolver()->getLevel(var(*nonassigned))==currentlevel){
			break;
		}
	}
	for(; nonassigned<trail.end(); nonassigned++){
		reportf("Possible conflict literal: "); gprintLit(*nonassigned); reportf("\n");
		for(vreifconstrptr::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
			if((*i)->getAtom()==var(*nonassigned) && !(*i)->isAssigned(space)){
				(*i)->propagate(!sign(*nonassigned), space);
				break;
			}
		}

		Search::Options searchOptions_;
		DFS<CPScript>* searchEngine_; // depth first search
		CPScript* enumerator_ = NULL;

		searchOptions_ = Search::Options::def;
		searchOptions_.stop = NULL; //new Search::MemoryStop(1000000000);

		searchEngine_ = new DFS<CPScript>(&space, searchOptions_);
		enumerator_ = searchEngine_->next();

		if(enumerator_==NULL){
			break;
		}
	}
	reportf("Conflicting literal: "); gprintLit(*nonassigned); reportf("\n");*/
	// END

	vec<Lit> clause;
	for(vector<Lit>::const_reverse_iterator i=trail.rbegin(); i<trail.rend(); i++){
		if(propagations.find(var(*i)) == propagations.end()){
			clause.push(~(*i));
		}
	}
	return getPCSolver()->addLearnedClause(clause);
}

// TODO do not propagate any more when search has been done successfully, until backtrack

rClause CPSolver::propagateAtEndOfQueue(){
	endenqueus++;

	/*if(endenqueus%25!=0){
		return nullPtrClause;
	}*/

	rClause confl = nullPtrClause;
	if (!isInitialized()) { return confl; }

	if(getPCSolver()->modes().verbosity>=3){
		cout << getSolverData()->getSpace() <<endl;
	}

	StatusStatistics stats;
	SpaceStatus status = getSolverData()->getSpace().status(stats);

	if(status == SS_FAILED){ //Conflict
		//reportf("Space failed during propagation \n");
		confl = genFullConflictClause();
		//reportf("Learned: "); Print::printClause(confl, getPCSolver()); reportf("\n");
		return confl;
	}

	if(getPCSolver()->modes().verbosity>=3){
		reportf("Propagated %d of %d literals\n", trail.size(), getSolverData()->getReifConstraints().size());
		cout <<getSolverData()->getSpace() <<endl;
	}

	if(getSolverData()->getReifConstraints().size()==trail.size()/* || endenqueus%50==0*/){
		reportf("Searching ");
		confl = propagateFinal();
		reportf(" Ended searching \n");
	}

	// If no conflict found , propagate all changes
	if(confl==nullPtrClause){
		// TODO duplicate with finishparsing
		for(vector<ReifiedConstraint*>::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
			if((*i)->isAssigned(getSolverData()->getSpace())){
				confl = notifySATsolverOfPropagation(mkLit((*i)->getAtom(), (*i)->isAssignedFalse(getSolverData()->getSpace())));
				if(confl!=nullPtrClause){
					return confl;
				}
			}
		}
	}

	return confl;
}

/**
 * does NOT have to be called when all booleans are decided
 */
rClause CPSolver::propagateFinal(){
	rClause confl = nullPtrClause;

	Search::Options searchOptions_;
	DFS<CPScript>* searchEngine_; // depth first search
	CPScript* enumerator_ = NULL;

	getSolverData()->getSpace().addBranchers();

	searchOptions_ = Search::Options::def;
	searchOptions_.stop = NULL; //new Search::MemoryStop(1000000000);

	searchEngine_ = new DFS<CPScript>(&getSolverData()->getSpace(), searchOptions_);
	enumerator_ = searchEngine_->next();

	if(enumerator_==NULL){
		if(searchEngine_->stopped()){
			throw idpexception("memory overflow on CP part");
		}else{
			if(getPCSolver()->modes().verbosity>=5){
				reportf("Conflict found in CP search.\n");
			}
			confl = genFullConflictClause();
		}
	}else{
		if(getSolverData()->getReifConstraints().size()==trail.size()){ //No @pre guarantee, so check!
			getSolverData()->replaceLastWith(enumerator_);
			cout <<*enumerator_<<endl;
		}
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
