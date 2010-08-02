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
