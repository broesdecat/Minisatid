#ifndef Hardware_h
#define Hardware_h

#include "FEnv.h"
#include "PbSolver.h"

namespace MiniSatPP {
class Solver;
class Linear;
struct PBOptions;
//=================================================================================================


int  estimatedAdderCost(const Linear& c);
void oddEvenSort(vec<Formula>& fs);
void pw_sort(vec<Formula>& fs);
void unarySortAdd(vec<Formula>& Xs,vec<Formula>& Ys,vec<Formula>& out_sorter,bool useShortCuts);
void rippleAdder(const vec<Formula>& xs, const vec<Formula>& ys, vec<Formula>& out);
void addPb(const vec<Formula>& ps, const vec<Int>& Cs_, vec<Formula>& out, int bits);

void clausify(Solver& s, PBOptions* options, const vec<Formula>& fs, vec<Lit>& out);
void clausify(Solver& s, PBOptions* options, const vec<Formula>& fs);


//=================================================================================================
}

#endif
