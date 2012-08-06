/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PRINT_HPP_
#define PRINT_HPP_

#include <iostream>
#include "utils/Utils.hpp"
#include "utils/PrintMessage.hpp"
#include "external/datastructuremacros.hpp"
#include "external/ExternalPrint.hpp"

namespace MinisatID {

class LiteralPrinter;

Lit getPrintableVar(Atom v);

template<typename S>
std::string toString(Atom obj, const S& solver) {
	return toString(getPrintableVar(obj), solver);
}

std::string toString(const Lit& obj, LiteralPrinter const * const solver);
std::string toString(const Lit& obj, const LiteralPrinter& solver);
std::string toString(const Lit& obj, lbool value, const LiteralPrinter& solver);

std::string toString(VarID id, const LiteralPrinter& solver);

}

#endif /* PRINT_HPP_ */
