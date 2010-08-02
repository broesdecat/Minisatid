#ifndef SATSOLVER_H_
#define SATSOLVER_H_

#ifdef USEMINISAT
class Solver;
#include "solver3minisat/Solver.h"
#endif
#ifdef USEMINISAT09Z
class Solver;
#include "solver3/Solver.hpp"
#endif
#ifdef USEMINISAT22
#include "solver3minisat22/core/Solver.h"
using namespace Minisat;
namespace Minisat{
	class Solver;
}
#endif



#endif// SATSOLVER_H_
