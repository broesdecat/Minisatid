/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef BASICSATUTILS_H_
#define BASICSATUTILS_H_

#include "satsolver/minisat/BasicSolverTypes.hpp"

namespace MinisatID {
	using Minisat::mkLit;
	using Minisat::Var;
	using Minisat::Lit;
	using Minisat::operator~;
	using Minisat::operator!;
	bool isPositive(const Lit& lit);
}

#endif// BASICSATUTILS_H_
