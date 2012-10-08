/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef EXTERNALPRINT_HPP_
#define EXTERNALPRINT_HPP_

#include "datastructuremacros.hpp"

namespace MinisatID {

template<class T>
T& operator<<(T& stream, const EqType& type) {
	switch (type) {
	case EqType::EQ:
		stream << "=";
		break;
	case EqType::NEQ:
		stream << "~=";
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
		stream << SUMSTR;
		break;
	case AggType::CARD:
		stream << CARDSTR;
		break;
	case AggType::MIN:
		stream << MINSTR;
		break;
	case AggType::MAX:
		stream << MAXSTR;
		break;
	case AggType::PROD:
		stream << PRODSTR;
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
	case ImplicationType::IMPLIES:
		stream << "=>";
		break;
	case ImplicationType::IMPLIEDBY:
		stream <<"<=";
		break;
	}
	return stream;
}

}

#endif /* EXTERNALPRINT_HPP_ */
