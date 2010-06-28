/*
 * CPSolver.hpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "solvers/PCSolver.hpp"

class PCSolver;

namespace CP {

/**
 * Class to interface with cp propagation (and who knows, search) engines.
 *
 * Interfacing with gecode:
 * 		include the correct hh files => http://www.gecode.org/doc-latest/reference/PageUsage.html
 *
 * 		gecode works as follows:
 * 			a "Space" obejct keeps the search space, domain, variables, ...
 * 			constraints, vars and domains can be added to the space
 * 			space has an operation "status" which propagates until fixpoint or failure
 */
class CPSolver {
	PCSolver * pcsolver;
public:
	CPSolver(PCSolver * pcsolver);
	virtual ~CPSolver();
};

}

#endif /* CPSOLVER_HPP_ */
