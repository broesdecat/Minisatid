/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "utils/Print.hpp"

#include <vector>
#include <iostream>

#include "satsolver/SATSolver.hpp"

#include "external/LiteralPrinter.hpp"

#include "modules/IDSolver.hpp"

using namespace std;
using namespace MinisatID;

namespace MinisatID{

Lit getPrintableVar(Atom v) { return mkPosLit(v); }

std::string toString(const Lit& lit, LiteralPrinter const * const solver){
	return toString(lit, *solver);
}

std::string toString(const Lit& lit, const LiteralPrinter& solver){
	return solver.toString(lit);
}

std::string toString(VarID id, const LiteralPrinter& solver){
	return solver.toString(id);
}

std::string toString(const Lit& lit, lbool value, const LiteralPrinter& solver){
	stringstream ss;
	ss <<solver.toString(lit) <<"(" <<(value==l_True?"T":(value==l_False?"F":"U")) <<")";
	return ss.str();
}
}
