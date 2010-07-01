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

using namespace Gecode;
using namespace std;

namespace CP {

/**
 * Mapping of variable-relation-value to Integer (SAT-atom)
 *
 * Initial loading: add ALL necessary SAT-atoms with respective mapping.
 *
 * Later, given a variable and (possibly reduced) domain: go over all atoms and check whether they
 * are true-false-unknown
 */

class CPScript: public Space{
public:
	CPScript(): Space(){

	}

	CPScript(bool share, CPScript& s): Space(share, s){
		//TODO copy members
	}

	virtual Space* copy(bool share){
		return new CPScript(share, *this);
	}
};

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
}

CPSolver::~CPSolver() {
}

}
