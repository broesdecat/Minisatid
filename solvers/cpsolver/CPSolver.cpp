/*
 * CPSolver.cpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#include <set>
#include <map>

#include "solvers/cpsolver/CPSolver.hpp"
#include "solvers/cpsolver/CPScript.hpp"

#include "solvers/cpsolver/CPUtils.hpp"

#include <solvers/cpsolver/Constraint.hpp>
#include <solvers/cpsolver/CPSolverData.hpp>

using namespace std;

namespace CP {
	class CPScript;
	class CPSolverData;
}

using namespace CP;

CPSolver::CPSolver(PCSolver * solver): init(true), pcsolver(solver), solverdata(new CPSolverData()) {

}

CPSolver::~CPSolver() {
}

void CPSolver::addTerm(int term, int min, int max){
	assert(init);
	solverdata->addTerm(TermIntVar(solverdata->getSpace(), term, min, max));
}

void CPSolver::addBinRel(int groundname, MINISAT::EqType rel, int bound, int atom){
	assert(init);
	TermIntVar lhs(solverdata->convertToVar(groundname));

	if(getSolver()->modes().verbosity>=10){
		cout <<"Added binary relation " <<gprintVar(atom) <<" <=> " <<lhs <<" " <<rel <<" "<<bound <<endl;
	}

	solverdata->addConstraint(new BinArithConstraint(solverdata->getSpace(), lhs, toRelType(rel), bound, atom));
}

void CPSolver::addBinRelVar(int groundname, MINISAT::EqType rel, int groundname2, int atom){
	assert(init);
	TermIntVar lhs(solverdata->convertToVar(groundname));
	TermIntVar rhs(solverdata->convertToVar(groundname2));

	if(getSolver()->modes().verbosity>=10){
		cout <<"Added binary relation " <<gprintVar(atom) <<" <=> " <<lhs <<" " <<rel <<" "<<rhs <<endl;
	}

	solverdata->addConstraint(new BinArithConstraint(solverdata->getSpace(), lhs, toRelType(rel), rhs, atom));
}

void CPSolver::addSum(vector<int> term, MINISAT::EqType rel, int bound, int atom){
	assert(init);
	vector<TermIntVar> set(solverdata->convertToVars(term));
	solverdata->addConstraint(new SumConstraint(solverdata->getSpace(), set, toRelType(rel), bound, atom));

	//FIXME: some simplifications/propagations are done immediately, so can be propagated sooner (to OTHER solvers)
}

void CPSolver::addSum(vector<int> term, vector<int> mult, MINISAT::EqType rel, int bound, int atom){
	assert(init);
	vector<TermIntVar> set(solverdata->convertToVars(term));
	solverdata->addConstraint(new SumConstraint(solverdata->getSpace(), set, mult, toRelType(rel), bound, atom));
}

void CPSolver::addSumVar(vector<int> term, MINISAT::EqType rel, int rhsterm, int atom){
	assert(init);
	vector<TermIntVar> set(solverdata->convertToVars(term));
	TermIntVar rhs(solverdata->convertToVar(rhsterm));
	solverdata->addConstraint(new SumConstraint(solverdata->getSpace(), set, toRelType(rel), rhs, atom));
}

void CPSolver::addSumVar(vector<int> term, vector<int> mult, MINISAT::EqType rel, int rhsterm, int atom){
	assert(init);
	vector<TermIntVar> set(solverdata->convertToVars(term));
	TermIntVar rhs(solverdata->convertToVar(rhsterm));
	solverdata->addConstraint(new SumConstraint(solverdata->getSpace(), set, mult, toRelType(rel), rhs, atom));

	//FIXME: some simplifications/propagations are done immediately, so can be propagated sooner (to OTHER solvers)
}

void CPSolver::addCount(vector<int> terms, MINISAT::EqType rel, int value, int rhsterm){
	assert(init);

	if(getSolver()->modes().verbosity>=10){
		cout <<"Added Count(";
		for(vector<int>::const_iterator i=terms.begin(); i<terms.end(); i++){
			cout << *i <<"=" <<value <<", ";
		}
		cout <<") " <<rel << " " <<rhsterm <<endl;
	}

	vector<TermIntVar> set(solverdata->convertToVars(terms));
	TermIntVar rhs(solverdata->convertToVar(rhsterm));
	/*solverdata->addConstraint(*/ //FIXME store them //FIXME make all constraints not-stack objects
	CountConstraint(solverdata->getSpace(), set, toRelType(rel), value, rhs);
	/*);*/
}

/*void CPSolver::addCount(vector<vector<string> > terms, MINISAT::EqType rel, vector<string> term){
	vector<TermIntVar> set;
	for(int i=0; i<terms.size(); i++){
		for(vector<TermIntVar>::const_iterator j=solverdata->getTerms().begin(); j<solverdata->getTerms().end(); j++){
			if((*j)==terms[i]){
				set.push_back(*j);
				break;
			}
		}
	}
	TermIntVar rhs;
	for(vector<TermIntVar>::const_iterator j=solverdata->getTerms().begin(); j<solverdata->getTerms().end(); j++){
		if((*j)==term){
			rhs = *j;
			break;
		}
	}
	//solverdata->addConstraint(
	//FIXME store them //FIXME make all constraints not-stack objects
	CountConstraint(*solverdata->getSpace(), set, toRelType(rel), rhs);
}*/

bool CPSolver::addAllDifferent(vector<int> term){
	assert(init);
	vector<TermIntVar> set(solverdata->convertToVars(term));
	//TODO not added to solverdata constraints!
	/*solverdata->getConstraints().push_back(*/new DistinctConstraint(solverdata->getSpace(), set);//);

	//TODO check failing of space here (and in all other ones too!).
	return true;
}

////////////////////////////
// SOLVER METHODS
////////////////////////////

bool CPSolver::finishParsing(){
	assert(init);
	init = false;

	vector<ReifiedConstraint*> assigned;
	for(vector<ReifiedConstraint*>::const_iterator i=solverdata->getConstraints().begin(); i<solverdata->getConstraints().end(); i++){
		if((*i)->isAssigned(solverdata->getSpace())){
			assigned.push_back(*i);
		}
	}

	StatusStatistics stats;
	SpaceStatus status = solverdata->getSpace().status(stats);

	if(status==SS_FAILED){
		return false;
	}

	for(vector<ReifiedConstraint*>::const_iterator i=solverdata->getConstraints().begin(); i<solverdata->getConstraints().end(); i++){

		//check if it was not already assigned
		bool alreadyassigned = false;
		for(vector<ReifiedConstraint*>::const_iterator j=assigned.begin(); j<assigned.end(); j++){
			if((*i)==(*j)){
				alreadyassigned = true;
			}
		}
		if(alreadyassigned){
			continue;
		}

		if((*i)->isAssignedTrue(solverdata->getSpace())){
			getSolver()->setTrue(mkLit((*i)->getAtom()));
		}else if((*i)->isAssignedFalse(solverdata->getSpace())){
			getSolver()->setTrue(mkLit((*i)->getAtom(), true));
		}
	}

	solverdata->addSpace();
	return true;
}

rClause CPSolver::propagate(Lit l){
	if (init) {return nullPtrClause;}

	//reportf("CP propagated: "); gprintLit(l); reportf(".\n");

	int constrindex = -1;
	rClause confl = nullPtrClause;
	for(int i=0; i<solverdata->getConstraints().size(); i++){
		if(solverdata->getConstraints()[i]->getAtom()==var(l)){
			constrindex = i;
			break;
		}
	}
	if(constrindex==-1){
		//reportf("No constraint within CP for that literal.\n");
		return confl;
	}

	trail.push_back(l);

	solverdata->getConstraints()[constrindex]->propagate(!sign(l), solverdata->getSpace());
	//FIXME check for failure here too (adding constraints also does simple checks)

	return confl;
}

void CPSolver::backtrack(){
	if(init){ return; }
	solverdata->backtrack();
}

void CPSolver::backtrack(Lit l){
	if(trail.size()>0 && l==trail.back()){
		trail.pop_back();
	}
}

rClause CPSolver::propagateAtEndOfQueue(){
	if (init) {return nullPtrClause;}

	rClause confl = nullPtrClause;
	StatusStatistics stats;
	SpaceStatus status = solverdata->getSpace().status(stats);
	//cout <<solverdata->getSpace() <<endl;

	if(status == SS_FAILED){
		//Conflict
		//Very simple clause generation:
		vec<Lit> clause;
		//FIXME should be of PREVIOUS space!
		//FIXME ADD STACK IN CORRECT ORDER! First add the conflicting one!
		for(vector<ReifiedConstraint*>::const_iterator i=solverdata->getConstraints().begin(); i<solverdata->getConstraints().end(); i++){
			if(isTrue((*i)->getBoolVar(solverdata->getSpace()))){
				clause.push(mkLit((*i)->getAtom(), true));
			}else if(isFalse((*i)->getBoolVar(solverdata->getSpace()))){
				clause.push(mkLit((*i)->getAtom()));
			}
		}
		for(int i=0; i<trail.size(); i++){
			clause.push(~trail[i]);
		}
		confl = getSolver()->makeClause(clause, true);
		//FIXME staat het hier juist?
		//pcsolver->addLearnedClause(confl);
	}else{
		if(solverdata->allBooleansKnown()){ //dmv counter als er een assigned wordt
			confl = propagateFinal();
		}
		if(confl==nullPtrClause){
			vector<Lit> atoms = solverdata->getBoolChanges();
			for(int i=0; i<atoms.size(); i++){
				if(getSolver()->value(atoms[i])==l_Undef){ //TODO niet de mooiste oplossing, maar momenteel ziet hij gepropageerde literals natuurlijk ook als changes
					getSolver()->setTrue(atoms[i], nullPtrClause);
				}

			}
		}
		solverdata->addSpace();
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
