#include "modules/aggsolver/AggUtils.hpp"

#include "modules/AggSolver.hpp"
#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "theorysolvers/PCSolver.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

using namespace std;
using namespace MinisatID;
using namespace Aggrs;

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool Aggrs::oppositeIsJustified(const WL& l, VarToJustif& currentjust, bool real, AggSolver const * const solver) {
	if (real) {
		return solver->value(l.getLit()) != l_True;
	} else {
		return solver->value(l.getLit()) != l_True && (!sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool Aggrs::isJustified(const WL& l, VarToJustif& currentjust, bool real, AggSolver const * const solver) {
	if (real) {
		return solver->value(l.getLit()) != l_False;
	} else {
		return solver->value(l.getLit()) != l_False && (sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool Aggrs::isJustified(Var x, VarToJustif& currentjust) {
	return currentjust[x] == 0;
}