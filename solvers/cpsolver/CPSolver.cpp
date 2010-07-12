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

#include <gecode/kernel.hh>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>
//#include "gecode/int/view.hpp"

using namespace Gecode;
using namespace std;

namespace CP {
IntRelType negate(IntRelType eq){
	switch (eq) {
		case Gecode::IRT_EQ:
			return Gecode::IRT_NQ;
		case Gecode::IRT_NQ:
			return Gecode::IRT_EQ;
		case Gecode::IRT_LQ:
			return Gecode::IRT_GR;
		case Gecode::IRT_GQ:
			return Gecode::IRT_LE;
		case Gecode::IRT_LE:
			return Gecode::IRT_GQ;
		case Gecode::IRT_GR:
			return Gecode::IRT_LQ;
	}
}

IntRelType toRelType(MINISAT::EqType eq){
	switch (eq) {
		case MINISAT::MEQ:
			return Gecode::IRT_EQ;
		case MINISAT::MNEQ:
			return Gecode::IRT_NQ;
		case MINISAT::MLEQ:
			return Gecode::IRT_LQ;
		case MINISAT::MGEQ:
			return Gecode::IRT_GQ;
		case MINISAT::ML:
			return Gecode::IRT_LE;
		case MINISAT::MG:
			return Gecode::IRT_GR;
	}
}

typedef vector<IntVar>::size_type termindex;
typedef vector<BoolVar>::size_type boolindex;

/**
 * Mapping of variable-relation-value to Integer (SAT-atom)
 *
 * Initial loading: add ALL necessary SAT-atoms with respective mapping.
 *
 * Later, given a variable and (possibly reduced) domain: go over all atoms and check whether they
 * are true-false-unknown
 */

class TermIntVar{
//private:
//	TermIntVar(TermIntVar&){}
public:
	vector<string> term; //First element is the function symbol, subsequent ones are the arguments
	int min, max;
	termindex var;

	TermIntVar():min(-1), max(-1), var(-1){

	}

	TermIntVar(CPScript& space, vector<string> groundterm, int min, int max)
		: term(groundterm), min(min), max(max), var(space.addIntVar(min, max)){
	}

	~TermIntVar(){}

	bool operator==(const TermIntVar& rhs) const{
		return this->operator ==(rhs.term);
	}

	bool operator==(const vector<string>& rhs) const{
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

//Let this solver decide whether to use a reified representation or not

class Constraint{
private:
	int atom;
	boolindex var;

public:
	Constraint(int atom, CPScript& space): atom(atom), var(space.addBoolVar()){
	}

	int getAtom() const { return atom; }

	/*virtual bool isReified(){
		return false;
	}*/

	bool isAssignedTrue(const CPScript& space) const{
		return space.isTrue(getBoolVar());
	}

	bool isAssignedFalse(const CPScript& space) const{
		return space.isFalse(getBoolVar());
	}

	bool isAssigned(const CPScript& space) const{
		return space.isAssigned(getBoolVar());
	}

	void propagate(bool becametrue, CPScript& space){
		assert(!isAssigned(space));
		cout <<"Before rel" << space.getBoolVars()[getBoolVar()] <<endl;
		//BoolVar v(space, 0, 1);
		//rel(space, v, IRT_GQ, becametrue?1:0);
		rel(space, space.getBoolVars()[getBoolVar()], IRT_GQ, becametrue?1:0);
		//Int::BoolView v(space.getBoolVars()[getBoolVar()]);
		//v.eq(space, becametrue?1:0);
	}

	boolindex getBoolVar() const { return var; }
};

class CPScript;

class SumConstraint: public Constraint{
private:
	vector<TermIntVar> set;
	IntRelType rel;

	bool intrhs;
	TermIntVar trhs;
	int irhs;

public:
	SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, TermIntVar rhs, int atom)
		: Constraint(atom, space), set(tset.size()), rel(rel), intrhs(false),
		  trhs(rhs){
		IntVarArgs ar(tset.size());
		for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
			set[i] = tset[i];
			ar[i] = space.getIntVars()[tset[i].var];
		}
		linear(space, ar, rel, space.getIntVars()[trhs.var], space.getBoolVars()[getBoolVar()]/*,consistency level*/);
	}

	SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int rhs, int atom)
		: Constraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs){
		IntVarArgs ar(tset.size());
		for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
			set[i] = tset[i];
			ar[i] = space.getIntVars()[tset[i].var];
		}
		linear(space, ar, rel, irhs, space.getBoolVars()[getBoolVar()]/*,consistency level*/);
	}

	/*bool isReified(){
		return true;
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
//			// is this a COPY or not???
//			set[i] = tset[i]->var;
//		}
//	}
//
//	/*void writeOut(Space& space){
//		distinct(space, set); // choose consistency
//	}
//
//	void writeNegationOut(Space& space){
//		// not possible, write out as clause?
//		//quadratic number of clauses needed
//		assert(false);
//	}*/
//};

//Atmostone NON REIF
//BinaryKnapSack (also LINEAR) REIF
//min max abs mult (arithmetic constraints) NON REIF
//count NON REIF
//Binary arith = , <=, ... REIF

/*template <class T>
void update(CPScript& space, bool share, T newt, T oldt){

}

template <>
void update(CPScript& space, bool share, TermIntVar newt, TermIntVar oldt){
	newt.var.update(space, share, oldt.var);
}*/

/*template <>
void update(Space& space, bool share, SumConstraint newt, SumConstraint oldt){
	newt.vars.update(space, share, oldt.vars);
}*/

class CPSolverData{
private:
	vector<CPScript*> history;
	vector<TermIntVar> terms;
	vector<Constraint*> constraints;

public:
	CPSolverData(){
		history.push_back(new CPScript());
	}

	~CPSolverData(){
		for(int i=0; i<constraints.size(); i++){
			delete constraints[i];
		}
	}

	CPScript* getSpace() const{ return history.back(); }
	void addSpace(){
		//getSpace()->operator <<(cout);
		cout << *getSpace() <<endl;
		history.push_back(getSpace()->copy(false));
	}
	void backtrack(){ history.pop_back(); }

	const vector<TermIntVar>& getTerms() const { return terms; }
	const vector<Constraint*>& getConstraints() const{ return constraints; }

	void addTerm(TermIntVar var){
		terms.push_back(var);
	}

	//owning pointer
	void addConstraint(Constraint* c){
		constraints.push_back(c);
	}

	bool allBooleansKnown() const{
		for(int i=0; i<getConstraints().size(); i++){
			if(!getConstraints()[i]->isAssigned(*getSpace())){
				return false;
			}
		}
		return true;
	}

	vector<Lit> getBoolChanges() const{
		vector<Lit> lits;
		for(int i=0; i<getConstraints().size(); i++){
			int boolvar = getConstraints()[i]->getBoolVar();
			BoolVar current = getSpace()->getBoolVars()[boolvar];
			BoolVar prev = history[history.size()-2]->getBoolVars()[boolvar];
			if(current.min() == current.max() && prev.min() != prev.max()){
				lits.push_back(Lit(getConstraints()[i]->getAtom(), current.min()==0));
			}
		}
		return lits;
	}
};

void CPSolver::addTerm(vector<string> term, int min, int max){
	solverdata->addTerm(TermIntVar(*solverdata->getSpace(), term, min, max));
}

void CPSolver::addSum(vector<vector<string> > term, MINISAT::EqType rel, int bound, int atom){
	vector<TermIntVar> set;
	for(int i=0; i<term.size(); i++){
		for(vector<TermIntVar>::const_iterator j=solverdata->getTerms().begin(); j<solverdata->getTerms().end(); j++){
			if((*j).operator ==(term[i])){
				set.push_back(*j);
				break;
			}
		}
	}
	solverdata->addConstraint(new SumConstraint(*solverdata->getSpace(), set, toRelType(rel), bound, atom));

	//FIXME: propagations here are done immediately, so also have to be propagated (to OTHER solvers)

/*	for(int i=0; i<solverdata->getConstraints().size(); i++){
		if(solverdata->getConstraints()[i]->isAssigned(*solverdata->getSpace())){
		}
	}*/
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


CPSolver::CPSolver(PCSolver * solver): init(true), pcsolver(solver), solverdata(new CPSolverData()) {

}

CPSolver::~CPSolver() {
}

Clause* CPSolver::propagate(Lit l){
	if (init) {return NULL;}

	int constrindex = -1;
	Clause* confl = NULL;
	for(int i=0; i<solverdata->getConstraints().size(); i++){
		if(solverdata->getConstraints()[i]->getAtom()==var(l)){
			constrindex = i;
			break;
		}
	}
	if(constrindex==-1){
		return confl;
	}

	solverdata->getConstraints()[constrindex]->propagate(!sign(l), *solverdata->getSpace());

	return confl;
}

void CPSolver::backtrack(){
	if(init){ return; }
	solverdata->backtrack();
}

Clause* CPSolver::propagateAtEndOfQueue(){
	if (init) {return NULL;}

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
			vector<Lit> atoms = solverdata->getBoolChanges();
			for(int i=0; i<atoms.size(); i++){
				pcsolver->setTrue(atoms[i], NULL);
			}
		}
	}

	solverdata->addSpace();

	return confl;
}

Clause* CPSolver::propagateFinal(){
	Clause* confl = NULL;
	//Options o("CPScript");
	//o.solutions(1);
	DFS<CPScript> d = DFS<CPScript>(solverdata->getSpace()/*, o*/);
	Space* newspace = d.next();
	if(newspace==NULL){
		//TODO add conflict clause
	}
	return confl;
}

bool CPSolver::finishParsing(){
	init = false;
	solverdata->addSpace();
	return true;
}

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
