/*
 * CPSolver.cpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#include <set>
#include <map>

#include "solvers/CPSolver.hpp"

#include "gecode/kernel.hh"
#include "gecode/driver.hh"
#include "gecode/int.hh"
#include "gecode/minimodel.hh"
//#include <gecode/int/view.hpp>

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

/*struct TermIntVar{
	vector<string> term; //First element is the function symbol, subsequent ones are the arguments
	vector<int> domain;
	IntVar var;

	bool operator==(const TermIntVar& rhs){
		vector<string>::const_iterator i=term.begin();
		vector<string>::const_iterator j=rhs.term.begin();
		if(rhs.term.size()!=term.size()){
			return false;
		}
		for(; i<term.end(); i++, j++){
			if(*i.compare(*j)){
				return false;
			}
		}
		return true;
	}
};*/
//
////Let this solver decide whether to use a reified representation or not
//
///*class SumConstraint{
//private:
//	IntVarArgs set;
//	IntRelType rel;
//
//	bool intrhs;
//	IntVar trhs;
//	int irhs;
//
//	int atom;
//
//public:
//	//not reified sum constraint
//	SumConstraint(vector<TermIntVar> set, IntRelType rel, TermIntVar rhs, int atom){
//		//this->set = set;
//		this->rel = rel;
//		//this->trhs = rhs;
//		this->intrhs = false;
//	}
//
//	SumConstraint(vector<TermIntVar> set, IntRelType rel, int rhs, int atom){
//		//this->set = set;
//		this->rel = rel;
//		this->irhs = rhs;
//		this->intrhs = true;
//	}
//
//	void writeOut(CPScript& space){
//		if(intrhs){
//			linear(space, set, rel, irhs);
//		}else{
//			linear(space, set, rel, trhs);
//		}
//	}
//};
//*/
//
//
CPSolver::CPSolver(PCSolver * solver):pcsolver(solver) {

	//TEST CODE, which works!
	Space* space = new CPScript();

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
	x.lq(space, 5);
}

CPSolver::~CPSolver() {
}

}
