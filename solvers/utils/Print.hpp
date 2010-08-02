/************************************************************************************[PCSolver.hpp]
Copyright (c) 2009-2010, Broes De Cat

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
#ifndef PRINT_HPP_
#define PRINT_HPP_

#include "solvers/SATSolver.h"
#include "solvers/pcsolver/PCSolver.hpp"
#include "solvers/idsolver/IDSolver.hpp"
#include "solvers/modsolver/SOSolverHier.hpp"
#include "solvers/aggsolver/AggSolver.hpp"
#include "solvers/cpsolver/CPSolver.hpp"

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

template<class S>
void printClause(rClause c, S const * const s);

template<>
void printClause(rClause c, PCSolver const * const s);

}

#endif /* PRINT_HPP_ */
