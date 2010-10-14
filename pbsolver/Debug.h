#ifndef Debug_h
#define Debug_h

#include "pbsolver/SolverTypes.h"
#include "pbsolver/PbSolver.h"
#include "pbsolver/ADTs/FEnv.h"


//=================================================================================================

namespace PBSolver{
extern vec<cchar*>* debug_names;

void dump(Int num);
void dump(Lit p);
void dump(Formula f);
void dump(const vec<Lit>& ps, const vec<Int>& Cs);
void dump(const vec<Lit>& ps, const vec<Int>& Cs, const vec<int>& assigns);
void dump(const vec<Formula>& ps, const vec<Int>& Cs);
void dump(const Linear& pb, const vec<int>& assigns);
void dump(const Linear& pb);
macro void dump(Linear* pb) { dump(*pb); }
}

//=================================================================================================
#endif
