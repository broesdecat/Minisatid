/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include <set>
#include <map>

#include "modules/CPSolver.hpp"
#include "modules/cpsolver/CPScript.hpp"

#include "modules/cpsolver/CPUtils.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "modules/cpsolver/Constraint.hpp"
#include "modules/cpsolver/CPSolverData.hpp"
#include "utils/Print.hpp"

using namespace std;

using namespace MinisatID;
using namespace MinisatID::Print;
using namespace MinisatID::CP;

using namespace Gecode;

CPSolver::CPSolver(PCSolver * solver): DPLLTmodule(solver), solverdata(new CPSolverData()),
		endenqueus(0){

}

CPSolver::~CPSolver() {
	delete solverdata;
}

// INITIALIZATION

// FIXME: reification atoms have to be unique! CHECK THIS

bool CPSolver::add(const InnerIntVar& form){
	assert(!isInitialized());
	getSolverData()->addTerm(TermIntVar(getSolverData()->getSpace(), form.varID, form.minvalue, form.maxvalue));
	return true;
}

bool CPSolver::add(const InnerCPBinaryRel& form){
	assert(!isInitialized());
	TermIntVar lhs(solverdata->convertToVar(form.varID));
	getSolverData()->addReifConstraint(new BinArithConstraint(getSolverData()->getSpace(), lhs, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPBinaryRelVar& form){
	assert(!isInitialized());
	TermIntVar lhs(getSolverData()->convertToVar(form.lhsvarID));
	TermIntVar rhs(getSolverData()->convertToVar(form.rhsvarID));
	getSolverData()->addReifConstraint(new BinArithConstraint(getSolverData()->getSpace(), lhs, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSum& form){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(form.varIDs));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWeighted& form){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(form.varIDs));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, form.weights, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWithVar& form){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(form.varIDs));
	TermIntVar rhs(getSolverData()->convertToVar(form.rhsvarID));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWeightedWithVar& form){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(form.varIDs));
	TermIntVar rhs(getSolverData()->convertToVar(form.rhsvarID));
	getSolverData()->addReifConstraint(new SumConstraint(getSolverData()->getSpace(), set, form.weights, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPCount& form){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(form.varIDs));
	TermIntVar rhs(getSolverData()->convertToVar(form.rhsvar));
	getSolverData()->addNonReifConstraint(new CountConstraint(getSolverData()->getSpace(), set, toRelType(form.rel), form.eqbound, rhs));
	return true;
}

bool CPSolver::add(const InnerCPAllDiff& form){
	assert(!isInitialized());
	vector<TermIntVar> set(getSolverData()->convertToVars(form.varIDs));
	getSolverData()->addNonReifConstraint(new DistinctConstraint(getSolverData()->getSpace(), set));
	return true;
}

// SOLVER METHODS

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
	return getPCSolver().createClause(lits, true);
}

rClause CPSolver::notifySATsolverOfPropagation(const Lit& p) {
	if (getPCSolver().value(p) == l_False) {
		if (getPCSolver().verbosity() >= 2) {
			//FIXME clog << ">> Deriving conflict in " <<p <<" because of the constraint TODO \n";
		}
		vector<Lit>::size_type temp = propreason[p];
		propreason[p] = trail.size();
		rClause confl = getExplanation(p);
		propreason[p] = temp;
		return confl;
	} else if (getPCSolver().value(p) == l_Undef) {
		if (getPCSolver().verbosity() >= 2) {
			//FIXME clog <<">> Deriving " <<p <<" because of the constraint expression TODO \n";
		}
		propreason[p] = trail.size();
		propagations.insert(var(p));
		getPCSolver().setTrue(p, this);
	} else {
		//NOOP
	}
	return nullPtrClause;
}

void CPSolver::finishParsing(bool& present, bool& unsat){
	assert(!isInitialized() && present && !unsat);
	notifyInitialized();

	// Propagate until fixpoint
	StatusStatistics stats;
	SpaceStatus status = getSolverData()->getSpace().status(stats);

	if(status==SS_FAILED){
		unsat = true;
		return;
	}

	// Propagate all assigned reification atoms. If any conflicts, return false
	for(vector<ReifiedConstraint*>::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
		if((*i)->isAssigned(getSolverData()->getSpace())){
			rClause confl = notifySATsolverOfPropagation(mkLit((*i)->getAtom(), (*i)->isAssignedFalse(getSolverData()->getSpace())));
			if(confl!=nullPtrClause){
				unsat = true;
				return;
			}
		}
	}
}

void CPSolver::notifyVarAdded(uint64_t nvars){
	//FIXME necessary/possible?
}

void CPSolver::newDecisionLevel(){
	//Add a new timepoint to the history
	getSolverData()->addSpace();
}

void CPSolver::backtrackDecisionLevels(int nblevels, int untillevel){
	getSolverData()->removeSpace(nblevels);
	//FIXME: backtrack per literal?
	/*if(trail.size()>0 && l==trail.back()){
		trail.pop_back();
		propagations.erase(var(l));
	}

	propreason[l] = -1;*/

}

rClause CPSolver::propagate(const Lit& l){
	rClause confl = nullPtrClause;
	if (!isInitialized()) { return confl; }

#ifdef DEBUG
	for(int i=0; i<trail.size(); i++){
		assert(var(trail[i])!=var(l));
	}
#endif

	for(vreifconstrptr::const_iterator i=getSolverData()->getReifConstraints().begin(); i<getSolverData()->getReifConstraints().end(); i++){
		if((*i)->getAtom()==var(l)){
			if(getPCSolver().modes().verbosity >= 5){
				//FIXME clog <<">> Propagated into CP: " <<l <<".\n";
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
	int currentlevel = getPCSolver().getLevel(var(trail.back()));
	reportf("Current level: %d\n", currentlevel);
	for(; nonassigned<trail.end(); nonassigned++){
		if(getPCSolver().getLevel(var(*nonassigned))==currentlevel){
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
	rClause c = getPCSolver().createClause(clause, true);
	getPCSolver().addLearnedClause(c);
	return c;
}

// TODO do not propagate any more when search has been done successfully, until backtrack

rClause CPSolver::propagateAtEndOfQueue(){
	endenqueus++;

	/*if(endenqueus%25!=0){
		return nullPtrClause;
	}*/

	rClause confl = nullPtrClause;
	if (!isInitialized()) { return confl; }

	if(getPCSolver().modes().verbosity>=3){
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

	if(getPCSolver().modes().verbosity>=3){
		clog <<"Propagated " <<trail.size() <<" of " <<getSolverData()->getReifConstraints().size() <<" literals\n";
		cout <<getSolverData()->getSpace() <<endl;
	}

	if(getSolverData()->getReifConstraints().size()==trail.size()/* || endenqueus%50==0*/){
		clog <<"Searching ";
		confl = propagateFinal();
		clog <<" Ended searching \n";
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
			if(getPCSolver().modes().verbosity>=5){
				clog <<"Conflict found in CP search.\n";
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

void CPSolver::printStatistics() const{
	//TODO
}

void CPSolver::print() const{
	//TODO
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
