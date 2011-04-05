/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
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

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
bool MinisatID::oppositeIsJustified(const WL& l, VarToJustif& currentjust, bool real, AggSolver const * const solver) {
	if (real) {
		return solver->value(l.getLit()) != l_True;
	} else {
		return solver->value(l.getLit()) != l_True && (!sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool MinisatID::isJustified(const WL& l, VarToJustif& currentjust, bool real, AggSolver const * const solver) {
	if (real) {
		return solver->value(l.getLit()) != l_False;
	} else {
		return solver->value(l.getLit()) != l_False && (sign(l.getLit()) || isJustified(var(l.getLit()), currentjust));
	}
}

bool MinisatID::isJustified(Var x, VarToJustif& currentjust) {
	return currentjust[x] == 0;
}
