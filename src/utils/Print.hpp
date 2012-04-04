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

namespace MinisatID {

class LiteralPrinter;

Lit getPrintableVar(Var v);

template<typename S>
std::string toString(Var obj, const S& solver) {
	return toString(getPrintableVar(obj), solver);
}

std::string toString(const Lit& obj, LiteralPrinter const * const solver);
std::string toString(const Lit& obj, lbool value, LiteralPrinter const * const solver);
std::string toString(const Lit& obj, const LiteralPrinter& solver);
std::string toString(const Lit& obj, lbool value, const LiteralPrinter& solver);

template<class T>
T& operator<<(T& stream, const EqType& type) {
	switch (type) {
	case EqType::EQ:
		stream << "=";
		break;
	case EqType::NEQ:
		stream << "!=";
		break;
	case EqType::L:
		stream << "<";
		break;
	case EqType::G:
		stream << ">";
		break;
	case EqType::GEQ:
		stream << ">=";
		break;
	case EqType::LEQ:
		stream << "=<";
		break;
	}
	return stream;
}

template<class T>
T& operator<<(T& stream, AggType type) {
	switch (type) {
	case AggType::SUM:
		stream << "sum";
		break;
	case AggType::CARD:
		stream << "card";
		break;
	case AggType::MIN:
		stream << "min";
		break;
	case AggType::MAX:
		stream << "max";
		break;
	case AggType::PROD:
		stream << "prod";
		break;
	}
	return stream;
}

template<class T>
T& operator<<(T& stream, ImplicationType type) {
	switch (type) {
	case ImplicationType::EQUIVALENT:
		stream << "<=>";
		break;
	case ImplicationType::IMPLIEDBY:
		stream << "<=";
		break;
	case ImplicationType::IMPLIES:
		stream << "=>";
		break;
	}
	return stream;
}

}

#endif /* PRINT_HPP_ */
