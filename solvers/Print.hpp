/*
 * Print.hpp
 *
 *  Created on: Jun 28, 2010
 *      Author: broes
 */

#ifndef PRINT_HPP_
#define PRINT_HPP_

#include "solver3/Solver.hpp"
#include "solvers/PCSolver.hpp"
#include "solvers/IDSolver.hpp"
#include "solvers/SOSolverHier.hpp"
#include "solvers/aggs/AggSolver.hpp"
#include "solvers/cpsolver/CPSolver.hpp"

class Solver;
class PCsolver;
class AggSolver;
class ModSolver;
class IDSolver;
class ModSolverData;
namespace CP{
	class CPSolver;
}

namespace Print {

template<class S>
void print(S const * const s);

template<>
void print(PCSolver const * const s);

template<>
void print(IDSolver const * const s);

template<>
void print(CP::CPSolver const * const s);

template<>
void print(AggSolver const * const s);

template<>
void print(Solver const * const s);

template<>
void print(ModSolver const * const s);

template<>
void print(ModSolverData const * const s);

template<class C>
void printClause(const C& c);

template<class C, class S>
void printClause(const C& c, S const * const s);

template<>
void printClause(const Clause& c, PCSolver const * const s);

}

#endif /* PRINT_HPP_ */
