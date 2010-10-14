#ifndef PbParser_h
#define PbParser_h

#include "pbsolver/PbSolver.h"
#include "pbsolver/ADTs/Global.h"

//=================================================================================================

namespace PBSolver{
void parse_PB_file(cchar* filename, PbSolver& solver, bool abort_on_error = true);
void parse_PB     (cchar* text    , PbSolver& solver, bool abort_on_error = true);

void parse_natlist_file(cchar* filename, PbSolver& solver, bool abort_on_error = true);
}

//=================================================================================================
#endif
