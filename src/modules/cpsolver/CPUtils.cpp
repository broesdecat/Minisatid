/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include <modules/cpsolver/CPUtils.hpp>

using namespace MinisatID;

using namespace Gecode;

bool MinisatID::isTrue(BoolVar var) {
	return var.assigned() && var.one();
}

bool MinisatID::isFalse(BoolVar var) {
	return var.assigned() && var.zero();
}

bool MinisatID::isAssigned(BoolVar var) {
	return var.assigned();
}

Gecode::IntRelType MinisatID::negate(IntRelType eq) {
	IntRelType g = Gecode::IRT_EQ;
	switch (eq) {
	case Gecode::IRT_EQ:
		g = Gecode::IRT_NQ;
		break;
	case Gecode::IRT_NQ:
		g = Gecode::IRT_EQ;
		break;
	case Gecode::IRT_LQ:
		g = Gecode::IRT_GR;
		break;
	case Gecode::IRT_GQ:
		g = Gecode::IRT_LE;
		break;
	case Gecode::IRT_LE:
		g = Gecode::IRT_GQ;
		break;
	case Gecode::IRT_GR:
		g = Gecode::IRT_LQ;
		break;
	}
	return g;
}

IntRelType MinisatID::toRelType(EqType eq) {
	IntRelType g = Gecode::IRT_EQ;
	switch (eq) {
	case EqType::EQ:
		g = Gecode::IRT_EQ;
		break;
	case EqType::NEQ:
		g = Gecode::IRT_NQ;
		break;
	case EqType::LEQ:
		g = Gecode::IRT_LQ;
		break;
	case EqType::GEQ:
		g = Gecode::IRT_GQ;
		break;
	case EqType::L:
		g = Gecode::IRT_LE;
		break;
	case EqType::G:
		g = Gecode::IRT_GR;
		break;
	}
	return g;
}

EqType MinisatID::toEqType(IntRelType eq) {
	auto g = EqType::EQ;
	switch (eq) {
	case Gecode::IRT_EQ:
		g = EqType::EQ;
		break;
	case Gecode::IRT_NQ:
		g = EqType::NEQ;
		break;
	case Gecode::IRT_LQ:
		g = EqType::LEQ;
		break;
	case Gecode::IRT_GQ:
		g = EqType::GEQ;
		break;
	case Gecode::IRT_LE:
		g = EqType::L;
		break;
	case Gecode::IRT_GR:
		g = EqType::G;
		break;
	}
	return g;
}

std::ostream& MinisatID::operator<<(std::ostream& stream, Gecode::IntRelType rel) {
	switch (rel) {
	case Gecode::IRT_EQ:
		stream << "=";
		break;
	case Gecode::IRT_NQ:
		stream << "!=";
		break;
	case Gecode::IRT_LQ:
		stream << "=<";
		break;
	case Gecode::IRT_GQ:
		stream << ">=";
		break;
	case Gecode::IRT_LE:
		stream << "<";
		break;
	case Gecode::IRT_GR:
		stream << ">";
		break;
	}
	return stream;
}
