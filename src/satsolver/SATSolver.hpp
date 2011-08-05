/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SATSOLVER_H_
#define SATSOLVER_H_

#ifdef USEMINISAT
#include "Solver.hpp"
#endif
#ifdef USEMINISAT09Z
#include "Solver.hpp"
#endif
#ifdef USEMINISAT22
#include "core/Solver.h"
#endif

namespace Minisat {
	class Solver;
}

namespace MinisatID{
	class PCSolver;
	Minisat::Solver* createSolver(MinisatID::PCSolver*);
}

#endif// SATSOLVER_H_
