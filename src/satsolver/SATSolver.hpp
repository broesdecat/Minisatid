//LICENSEPLACEHOLDER
#ifndef SATSOLVER_H_
#define SATSOLVER_H_

#ifdef USEMINISAT
#include "solver3minisat/Solver.h"
#endif
#ifdef USEMINISAT09Z
#include "solver3/Solver.hpp"
#endif
#ifdef USEMINISAT22
#include "solver3minisat22/core/Solver.h"
#endif

namespace Minisat {
	class Solver;
}

namespace MinisatID{
	class PCSolver;
	Minisat::Solver* createSolver(MinisatID::PCSolver&);
}

#endif// SATSOLVER_H_
