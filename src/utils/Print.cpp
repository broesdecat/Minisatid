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

#include "constraintvisitors/LiteralPrinter.hpp"

#include "modules/IDSolver.hpp"

using namespace std;
using namespace MinisatID;

namespace MinisatID{

Lit getPrintableVar(Var v) { return mkPosLit(v); }

std::string print(const Lit& lit, LiteralPrinter const * const solver){
	return print(lit, *solver);
}

std::string print(const Lit& lit, lbool value, LiteralPrinter const* const solver){
	return print(lit, value, *solver);
}

std::string print(const Lit& lit, const LiteralPrinter& solver){
	return solver.printLiteral(lit);
}

std::string print(const Lit& lit, lbool value, const LiteralPrinter& solver){
	stringstream ss;
	ss <<solver.printLiteral(lit) <<"(" <<(value==l_True?"T":(value==l_False?"F":"U")) <<")";
	return ss.str();
}
}
