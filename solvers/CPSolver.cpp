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
	//TODO copy members
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

class SumConstraint{
private:
	IntVarArgs set;
	IntRelType rel;

	bool intrhs;
	IntVar trhs;
	int irhs;

	int atom;

public:
	//not reified sum constraint

	SumConstraint(vector<TermIntVar*> tset, IntRelType rel, TermIntVar rhs, int atom)
		: set(tset.size()), rel(rel), intrhs(false), trhs(rhs.var){
		for(vector<TermIntVar*>::size_type i=0; i<tset.size(); i++){
			//FIXME is this a COPY or not???
			set[i] = tset[i]->var;
		}
	}

	SumConstraint(vector<TermIntVar*> tset, IntRelType rel, int rhs, int atom)
		: set(tset.size()), rel(rel), intrhs(true), irhs(rhs){
		for(vector<TermIntVar*>::size_type i=0; i<tset.size(); i++){
			//FIXME is this a COPY or not???
			set[i] = tset[i]->var;
		}
	}

	SumConstraint(IntVarArgs set, IntRelType rel, IntVar rhs, int atom)
		: set(set), rel(rel), intrhs(false), trhs(rhs){
	}

	SumConstraint(IntVarArgs set, IntRelType rel, int rhs, int atom)
		: set(set), rel(rel), intrhs(true), irhs(rhs){
	}

	void writeOut(Space& space){
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
	}

	int getAtom() { return atom; }
};

class CPSolverData{
private:
	Space* space;
	vector<TermIntVar*> vars;
	vector<SumConstraint*> sums;

public:
	CPSolverData(): space(new CPScript()){
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

	Space* getSpace(){ return space; }
	vector<TermIntVar*>& getTerms() { return vars; }
	vector<SumConstraint*>& getSums() { return sums; }
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
	solverdata->getSums().push_back(new SumConstraint(set, toRelType(rel), bound, atom));
}


CPSolver::CPSolver(PCSolver * solver):pcsolver(solver), solverdata(new CPSolverData()) {

}

CPSolver::~CPSolver() {
}

Clause* CPSolver::propagateLiteral(Lit l){
	SumConstraint* f = NULL;
	for(vector<SumConstraint*>::const_iterator i=solverdata->getSums().begin(); i<solverdata->getSums().end(); i++){
		if((*i)->getAtom()==var(l)){
			f = *i;
			break;
		}
	}
	if(f==NULL){
		return NULL;
	}

	if(sign(l)){
		f->writeNegationOut(*solverdata->getSpace());
	}else{
		f->writeOut(*solverdata->getSpace());
	}

	return NULL; //FIXME
}

}
