/*
 * CPSolver.cpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#include "solvers/CPSolver.hpp"

#include "gecode/kernel.hh"
#include "gecode/driver.hh"
#include "gecode/int.hh"
#include "gecode/minimodel.hh"

using namespace Gecode;

namespace CP {

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
	Space* space = new CPScript();

	SizeOptions opt("Test configuration");
	opt.icl(ICL_DOM);
	opt.size(18);

	int periods = 10;
	IntArgs rh(periods), ra(periods), rg(periods);
	IntVarArgs n(periods);

	for (int p=0; p<periods; p++){
		n[p].init(*space,0,periods-1);
	}

	distinct(*space, n, opt.icl());
}

CPSolver::~CPSolver() {
}

}
