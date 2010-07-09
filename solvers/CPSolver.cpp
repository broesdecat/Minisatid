/*
 * CPSolver.cpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#include <set>
#include <map>

#include "solvers/CPSolver.hpp"

#include <gecode/kernel.hh>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>
//#include "gecode/int/view.hpp"

using namespace Gecode;
using namespace std;

namespace CP {
//
class CPScript: public Space{
public:
	CPScript();
	CPScript(bool share, CPScript& s);
	virtual Space* copy(bool share);
};

CPScript::CPScript(): Space(){

}

CPScript::CPScript(bool share, CPScript& s): Space(share, s){
	//TODO copy CPScript-specific members
}

Space* CPScript::copy(bool share){
	return new CPScript(share, *this);
}


/**
 * Mapping of variable-relation-value to Integer (SAT-atom)
 *
 * Initial loading: add ALL necessary SAT-atoms with respective mapping.
 *
 * Later, given a variable and (possibly reduced) domain: go over all atoms and check whether they
 * are true-false-unknown
 */

struct TermIntVar{
	vector<string> term; //First element is the function symbol, subsequent ones are the arguments
	int min, max;
	IntVar var;

	TermIntVar(Space& space, vector<string> groundterm, int min, int max)
		: term(groundterm), min(min), max(max), var(space, min, max){
	}

	bool operator==(const TermIntVar& rhs){
		return this->operator ==(rhs.term);
	}

	bool operator==(const vector<string>& rhs){
		vector<string>::const_iterator i=term.begin();
		vector<string>::const_iterator j=rhs.begin();
		if(rhs.size()!=term.size()){
			return false;
		}
		for(; i<term.end(); i++, j++){
			if((*i).compare(*j)){
				return false;
			}
		}
		return true;
	}
};

IntRelType negate(IntRelType eq){
	switch (eq) {
		case Gecode::IRT_EQ:
			return Gecode::IRT_NQ;
			break;
		case Gecode::IRT_NQ:
			return Gecode::IRT_EQ;
			break;
		case Gecode::IRT_LQ:
			return Gecode::IRT_GR;
			break;
		case Gecode::IRT_GQ:
			return Gecode::IRT_LE;
			break;
		case Gecode::IRT_LE:
			return Gecode::IRT_GQ;
			break;
		case Gecode::IRT_GR:
			return Gecode::IRT_LQ;
			break;
		default:
			break;
	}
}

//Let this solver decide whether to use a reified representation or not

class Constraint{
private:
	int atom;

public:
	Constraint(int atom): atom(atom){}

	int getAtom() { return atom; }

	virtual void writeOut(Space& space) = 0;
	virtual void writeNegationOut(Space& space) = 0;

	virtual bool isReified(){
		return false;
	}

	virtual bool isAssignedTrue() = 0;
	virtual bool isAssignedFalse() = 0;
};

class SumConstraint: public Constraint{
private:
	IntVarArgs set;
	IntRelType rel;
	BoolVar var;

	bool intrhs;
	IntVar trhs;
	int irhs;

public:
	SumConstraint(Space& space, vector<TermIntVar*> tset, IntRelType rel, TermIntVar rhs, int atom)
		: Constraint(atom), set(tset.size()), rel(rel), intrhs(false), trhs(rhs.var),
		  var(BoolVar(space, 0, 1)){
		for(vector<TermIntVar*>::size_type i=0; i<tset.size(); i++){
			//FIXME is this a COPY or not???
			set[i] = tset[i]->var;
		}
		linear(space, set, rel, trhs, var/*,consistency level*/);
	}

	SumConstraint(Space& space, vector<TermIntVar*> tset, IntRelType rel, int rhs, int atom)
		: Constraint(atom), set(tset.size()), rel(rel), intrhs(true), irhs(rhs),
		  var(BoolVar(space, 0, 1)){
		for(vector<TermIntVar*>::size_type i=0; i<tset.size(); i++){
			//FIXME is this a COPY or not???
			set[i] = tset[i]->var;
		}
		linear(space, set, rel, irhs, var/*,consistency level*/);
	}

	bool isReified(){
		return true;
	}

	void writeOut(Space& space){
		var.one();
	}

	void writeNegationOut(Space& space){
		var.zero();
	}

	bool isAssignedTrue(){
		return var.min()==1;
	}
	bool isAssignedFalse(){
		return var.max()==0;
	}

	/*void writeOut(Space& space){
		if(intrhs){
			linear(space, set, rel, irhs); //TODO choose consistency
		}else{
			linear(space, set, rel, trhs); //TODO choose consistency
		}
	}

	void writeNegationOut(Space& space){
		if(intrhs){
			linear(space, set, negate(rel), irhs); //TODO choose consistency
		}else{
			linear(space, set, negate(rel), trhs); //TODO choose consistency
		}
	}*/
};

//class DistinctConstraint: public Constraint{
//private:
//	IntVarArgs set;
//public:
//	//not reified distinct constraint
//
//	DistinctConstraint(vector<TermIntVar*> tset, int atom)
//		: Constraint(atom), set(tset.size()){
//		for(vector<TermIntVar*>::size_type i=0; i<tset.size(); i++){
//			//FIXME is this a COPY or not???
//			set[i] = tset[i]->var;
//		}
//	}
//
//	/*void writeOut(Space& space){
//		distinct(space, set); //TODO choose consistency
//	}
//
//	void writeNegationOut(Space& space){
//		//TODO not possible, write out as clause?
//		//quadratic number of clauses needed
//		assert(false);
//	}*/
//};

//Atmostone NON REIF
//BinaryKnapSack (also LINEAR) REIF
//min max abs mult (arithmetic constraints) NON REIF
//count NON REIF
//Binary arith = , <=, ... REIF

/**
 * The new propagator that will be registered to all boolean change events
 */
class DPLLTPropagator: public Propagator{
protected:
  /// Constructor for posting
	DPLLTPropagator(Home home, ViewArray<View>& x): Propagator(home){

	}
  /// Constructor for cloning \a p
	DPLLTPropagator(Space& home, bool share, DPLLTPropagator& p): Propagator(home){

	}
public:
  /// Copy propagator during cloning
  virtual Actor*     copy(Space& home, bool share){

  }
  /// Perform propagation
  virtual ExecStatus propagate(Space& home, const ModEventDelta& med){

  }
  /// Post propagator for view array \a x
  static ExecStatus post(Home home, ViewArray<BoolView>& x){
	  new (home) Val<View>(home,x);
	  return ES_OK;
  }
};

void
dpllprop(Home home, const BoolVarArgs& x) {
	if (home.failed()) return;
	ViewArray<BoolView> xv(home,x);
	GECODE_ES_FAIL(DPLLTPropagator::post(home,xv));
}

class CPSolverData{
private:
	vector<TermIntVar*> vars;
	vector<Constraint*> constraints;
	vector<Space*> history;

public:
	CPSolverData(){
		Space* space = new CPScript();
		history.push_back(space);

		SizeOptions opt("Test configuration");
		opt.icl(ICL_DOM);
		opt.size(18);

		int periods = 10;
		IntVarArgs n(periods);
		IntVar n2;

		for (int p=0; p<periods; p++){
			n[p].init(*space,1,10);
		}

		distinct(*space, n, opt.icl());

		StatusStatistics* s = new StatusStatistics();
		SpaceStatus status = space->status(*s);
		if(status==SS_FAILED){
			reportf("No solution\n");
		}else if(status==SS_SOLVED){
			reportf("Solution found\n");
		}else{
			reportf("Choices left to make\n");
		}

		Gecode::Int::IntView x;
		x.lq(*space, 5);
	}

	Space* getSpace(){ return history.back(); }
	void backtrack(){ history.pop_back(); }
	vector<TermIntVar*>& getTerms() { return vars; }
	vector<Constraint*>& getConstraints() { return constraints; }
};

void CPSolver::addTerm(vector<string> term, int min, int max){
	solverdata->getTerms().push_back(new TermIntVar(*solverdata->getSpace(), term, min, max));

}

IntRelType toRelType(CPSolver::EqType eq){
	switch (eq) {
		case CPSolver::CPEQ:
			return Gecode::IRT_EQ;
			break;
		case CPSolver::CPNEQ:
			return Gecode::IRT_NQ;
			break;
		case CPSolver::CPLEQ:
			return Gecode::IRT_LQ;
			break;
		case CPSolver::CPGEQ:
			return Gecode::IRT_GQ;
			break;
		case CPSolver::CPL:
			return Gecode::IRT_LE;
			break;
		case CPSolver::CPG:
			return Gecode::IRT_GR;
			break;
		default:
			break;
	}
}

void CPSolver::addSum(vector<vector<string> > term, EqType rel, int bound, int atom){
	vector<TermIntVar*> set;
	for(int i=0; i<term.size(); i++){
		for(vector<TermIntVar*>::const_iterator j=solverdata->getTerms().begin(); j<solverdata->getTerms().end(); j++){
			if((*j)->operator ==(term[i])){
				set.push_back(*j);
				break;
			}
		}
	}
	solverdata->getConstraints().push_back(new SumConstraint(*solverdata->getSpace(), set, toRelType(rel), bound, atom));
}

void CPSolver::addAllDifferent(vector<vector<string> > term, int atom){
/*	vector<TermIntVar*> set;
	for(int i=0; i<term.size(); i++){
		for(vector<TermIntVar*>::const_iterator j=solverdata->getTerms().begin(); j<solverdata->getTerms().end(); j++){
			if((*j)->operator ==(term[i])){
				set.push_back(*j);
				break;
			}
		}
	}
	solverdata->getConstraints().push_back(new DistinctConstraint(set, atom));*/
}


CPSolver::CPSolver(PCSolver * solver):pcsolver(solver), solverdata(new CPSolverData()) {

}

CPSolver::~CPSolver() {
}

Clause* CPSolver::propagateLiteral(Lit l){
	//TODO only if l is still unknown!!!

	Constraint* f = NULL;
	Clause* confl = NULL;
	for(vector<Constraint*>::const_iterator i=solverdata->getConstraints().begin(); i<solverdata->getConstraints().end(); i++){
		if((*i)->getAtom()==var(l)){
			f = *i;
			break;
		}
	}
	if(f==NULL){
		return confl;
	}

	if(sign(l)){
		f->writeNegationOut(*solverdata->getSpace());
	}else{
		f->writeOut(*solverdata->getSpace());
	}

	return confl;
}

void CPSolver::backtrack(){
	solverdata->backtrack();
}

Clause* CPSolver::propagateAtEndOfQueue(){
	//TODO remember if there were any changes

	Clause* confl = NULL;
	StatusStatistics stats;
	SpaceStatus status = solverdata->getSpace()->status(stats);

	if(status == SS_FAILED){
		//Conflict
		//Very simple clause generation:
		vec<Lit> clause;
		//TODO should be of PREVIOUS space!
		/* ADD STACK IN CORRECT ORDER!
		 * for(vector<Constraint*>::const_iterator i=solverdata->getConstraints().begin(); i<solverdata->getConstraints().end(); i++){
			if((*i)->getAtom()==var(l)){
				continue;
			}
			if((*i)->isAssignedTrue()){
				clause.push(Lit((*i)->getAtom(), true));
			}else if((*i)->isAssignedFalse()){
				clause.push(Lit((*i)->getAtom()));
			}
		}*/
		confl = Clause_new(clause, true);
	}else{
		if(solverdata->allBooleansKnown()){ //dmv counter als er een assigned wordt
			confl = propagateFinal();
		}
		if(confl==NULL){
			for(vector<Constraint*>::const_iterator i=solverdata->getConstraints().begin(); i<solverdata->getConstraints().end(); i++){
				//if((*i)->isNewlyAssigned()){
					//FIXME propagate to solver
				//}
			}
		}
	}

	return confl;
}

Clause* CPSolver::propagateFinal(){
	Clause* confl = NULL;
	Options o;
	o.solutions(1);
	DFS<CPScript> d = DFS<CPScript>(solverdata->getSpace(), o);
	Space* newspace = d.next();
	if(newspace==NULL){
		//TODO add conflict clause
	}
	return confl;
}

}
