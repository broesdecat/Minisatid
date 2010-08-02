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
#ifndef SATUTILS_H_
#define SATUTILS_H_

#ifdef USEMINISAT
#include "mtlold/Vec.h"
#include "mtlold/Queue.h"
#include "mtlold/Heap.h"
#include "mtlold/Sort.h"
#include "solver3minisat/SolverTypes.h"
typedef Clause& pClause;
typedef Clause* rClause;

Lit mkLit(Var x, bool sign = false);
#endif

#ifdef USEMINISAT09Z
#include "mtlold/Vec.h"
#include "mtlold/Queue.h"
#include "mtlold/Heap.h"
#include "mtlold/Sort.h"
#include "solver3/SolverTypes.hpp"
typedef Clause& pClause;
typedef Clause* rClause;

Lit mkLit(Var x, bool sign = false);
#endif

#ifdef USEMINISAT22
#include "mtl/Vec.h"
#include "mtl/Queue.h"
#include "mtl/Heap.h"
#include "mtl/Sort.h"
#include "core/SolverTypes.h"
typedef Minisat::CRef pClause;
typedef Minisat::CRef rClause;
#endif

extern rClause nullPtrClause;
rClause getClauseRef(rClause rc);

#endif// SATSOLVER_H_
