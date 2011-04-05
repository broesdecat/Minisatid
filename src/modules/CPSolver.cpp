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
using namespace Gecode;

//FIXME use trail in aggsolver
//FIXME include cp model in printing of models


LitTrail::LitTrail(){
	trailindexoflevel.push_back(trail.size());
}
void LitTrail::newDecisionLevel(){
	trailindexoflevel.push_back(trail.size());
}
void LitTrail::backtrackDecisionLevels(int nbevels, int untillevel){
	vector<Var>::size_type earliest = trailindexoflevel[(uint)untillevel+1];
	while(trail.size()>earliest){
		values[var(trail.back())] = l_Undef;
		trail.pop_back();
	}

	for(int nb = 0; nb<nbevels; nb++){
		trailindexoflevel.pop_back();
	}
}
void LitTrail::propagate(const Lit& l){
	trail.push_back(l);
	values[var(l)] = sign(l)?l_False:l_True;
}
lbool LitTrail::value(const Lit& l) const{
	map<Var, lbool>::const_iterator it = values.find(var(l));
	if(it==values.end()){
		return l_Undef;
	}
	return (*it).second;
}

CPSolver::CPSolver(PCSolver * solver):
		DPLLTmodule(solver), solverdata(new CPSolverData()),
		searchedandnobacktrack(false){

}

CPSolver::~CPSolver() {
	delete solverdata;
}

const CPScript&	CPSolver::getSpace() const {
	return getData().getSpace();
}
CPScript& CPSolver::getSpace(){
	return getData().getSpace();
}

TermIntVar CPSolver::convertToVar(uint term) const{
	return getData().convertToVar(term);
}
vtiv CPSolver::convertToVars(const std::vector<uint>& terms) const{
	return getData().convertToVars(terms);
}

// INITIALIZATION

bool CPSolver::add(const InnerIntVar& form){
	assert(!isInitialized());
	getData().addTerm(TermIntVar(getSpace(), form.varID, form.minvalue, form.maxvalue));
	return true;
}

bool CPSolver::add(const InnerCPBinaryRel& form){
	assert(!isInitialized());
	TermIntVar lhs(convertToVar(form.varID));
	getData().addReifConstraint(new BinArithConstraint(getSpace(), lhs, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPBinaryRelVar& form){
	assert(!isInitialized());
	TermIntVar lhs(convertToVar(form.lhsvarID));
	TermIntVar rhs(convertToVar(form.rhsvarID));
	getData().addReifConstraint(new BinArithConstraint(getSpace(), lhs, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSum& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	getData().addReifConstraint(new SumConstraint(getSpace(), set, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWeighted& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	getData().addReifConstraint(new SumConstraint(getSpace(), set, form.weights, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWithVar& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	TermIntVar rhs(convertToVar(form.rhsvarID));
	getData().addReifConstraint(new SumConstraint(getSpace(), set, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWeightedWithVar& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	TermIntVar rhs(convertToVar(form.rhsvarID));
	getData().addReifConstraint(new SumConstraint(getSpace(), set, form.weights, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPCount& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	TermIntVar rhs(convertToVar(form.rhsvar));
	getData().addNonReifConstraint(new CountConstraint(getSpace(), set, toRelType(form.rel), form.eqbound, rhs));
	return true;
}

bool CPSolver::add(const InnerCPAllDiff& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	getData().addNonReifConstraint(new DistinctConstraint(getSpace(), set));
	return true;
}

// SOLVER METHODS

// Space management:
//		First space = space after adding all constraints and propagating until fixpoint
//		Any subsequent space is after adding ALL propagations of a decision level and propagating until fixpoint
//			so this can be MULTIPLE fixpoint propagations until next decision level!

rClause CPSolver::getExplanation(const Lit& p){
	// IMPORTANT: reason is necessary, because a literal might be derived by CP, but
	// requested an explanation before it is effectively propagated and in the trail itself

	assert(propreason[p]!=-1);

	vec<Lit> lits;
	lits.push(p);
	for(vector<Lit>::size_type i=0; i<propreason[p]; i++){
		// FIXME skip all those not propagated into the cp solver
		lits.push(~trail.getTrail()[i]);
	}
	return getPCSolver().createClause(lits, true);
}

rClause CPSolver::notifySATsolverOfPropagation(const Lit& p) {
	if (getPCSolver().value(p) == l_False) {
		if (getPCSolver().verbosity() >= 2) {
			clog<< ">> Deriving conflict in " <<p <<" because of constraint expression (printing not implemented)\n"; //TODO
		}
		vector<Lit>::size_type temp = propreason[p];
		propreason[p] = trail.getTrail().size();
		rClause confl = getExplanation(p);
		propreason[p] = temp;
		return confl;
	} else if (getPCSolver().value(p) == l_Undef) {
		if (getPCSolver().verbosity() >= 2) {
			clog <<">> Deriving " <<p <<" because of constraint expression (printing not implemented)\n"; //TODO
		}
		propreason[p] = trail.getTrail().size();
		getPCSolver().setTrue(p, this);
	} else {
		//NOOP
	}
	return nullPtrClause;
}

void CPSolver::checkHeadUniqueness() const{
	set<Var> heads;
	for(vector<ReifiedConstraint*>::const_iterator i=getData().getReifConstraints().begin(); i<getData().getReifConstraints().end(); i++){
		if(heads.find((*i)->getHead())!=heads.end()){
			stringstream ss;
			ss <<"Constraint reification atoms should be unique, but " <<(*i)->getHead() <<" is shared by at least two constraints.\n";
			throw idpexception(ss.str());
		}
		heads.insert((*i)->getHead());
	}
}

void CPSolver::finishParsing(bool& present, bool& unsat){
	assert(!isInitialized() && present && !unsat);

	checkHeadUniqueness();

	// Propagate until fixpoint
	StatusStatistics stats;
	SpaceStatus status = getSpace().status(stats);

	if(status==SS_FAILED){
		unsat = true;
	}

	// Propagate all assigned reification atoms.
	if(!unsat && propagateReificationConstraints()!=nullPtrClause){
		unsat = true;
	}

	return;
}

void CPSolver::notifyVarAdded(uint64_t nvars){}

void CPSolver::newDecisionLevel(){
	getData().addSpace();
	trail.newDecisionLevel();
}

void CPSolver::backtrackDecisionLevels(int nblevels, int untillevel){
	getData().removeSpace(nblevels);
	searchedandnobacktrack = false;
	trail.backtrackDecisionLevels(nblevels, untillevel);
}

rClause CPSolver::propagate(const Lit& l){
	rClause confl = nullPtrClause;
	if(!isInitialized()) { return confl; }
	if(searchedandnobacktrack){ return confl; }

	//Check if any constraint matched (might be turned into map)
	ReifiedConstraint* constr = NULL;
	for(reifconstrlist::const_iterator i=getData().getReifConstraints().begin(); i<getData().getReifConstraints().end(); i++){
		if((*i)->getHead()==var(l)){
			constr = *i;
			break;
		}
	}

	if(constr!=NULL){
		if(getPCSolver().modes().verbosity >= 5){
			clog <<">> Propagated into CP: " <<l <<".\n";
		}

		trail.propagate(l);
		if(!constr->isAssigned(getSpace())){
			confl = constr->propagate(!sign(l), getSpace());
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
	for(vector<Lit>::const_reverse_iterator i=trail.getTrail().rbegin(); i<trail.getTrail().rend(); i++){
		//FIXME skip all literals that were propagated BY the CP solver
		clause.push(~(*i));
	}
	rClause c = getPCSolver().createClause(clause, true);
	getPCSolver().addLearnedClause(c);
	return c;
}

rClause CPSolver::propagateReificationConstraints(){
	rClause confl = nullPtrClause;
	for(vector<ReifiedConstraint*>::const_iterator i=getData().getReifConstraints().begin(); confl==nullPtrClause && i<getData().getReifConstraints().end(); i++){
		if((*i)->isAssigned(getSpace())){
			confl = notifySATsolverOfPropagation(mkLit((*i)->getHead(), (*i)->isAssignedFalse(getSpace())));
		}
	}
	return confl;
}

rClause CPSolver::propagateAtEndOfQueue(){
	rClause confl = nullPtrClause;
	if (!isInitialized()) { return confl; }
	if(searchedandnobacktrack){ return confl; }

	StatusStatistics stats;
	SpaceStatus status = getSpace().status(stats);

	if(status == SS_FAILED){ //Conflict
		return genFullConflictClause();
	}

	if(verbosity()>=3){
		clog <<"Propagated " <<trail.getTrail().size() <<" of " <<getData().getReifConstraints().size() <<" literals\n";
	}

	if(getData().getReifConstraints().size()==trail.getTrail().size()){
		confl = propagateFinal();
		searchedandnobacktrack = true;
	}

	if(confl==nullPtrClause){
		confl = propagateReificationConstraints();
	}

	return confl;
}

rClause CPSolver::propagateFinal(){
	rClause confl = nullPtrClause;

	Search::Options searchOptions_;
	DFS<CPScript>* searchEngine_; // depth first search
	CPScript* enumerator_ = NULL;

	getSpace().addBranchers();

	searchOptions_ = Search::Options::def;
	searchOptions_.stop = NULL; //new Search::MemoryStop(1000000000);

	searchEngine_ = new DFS<CPScript>(&getSpace(), searchOptions_);
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
		if(getData().getReifConstraints().size()==trail.getTrail().size()){ //No @pre guarantee, so check!
			getData().replaceLastWith(enumerator_);
		}
	}

	return confl;
}

void CPSolver::printStatistics() const{
	//TODO
}

void CPSolver::printState() const{
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
