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
using namespace CP;

using namespace Gecode;

bool CP::isTrue(Gecode::BoolVar var){
	return var.assigned() && var.one();
}

bool CP::isFalse(Gecode::BoolVar var) {
	return var.assigned() && var.zero();
}

bool CP::isAssigned(Gecode::BoolVar var){
	return var.assigned();
}

Gecode::IntRelType CP::negate(Gecode::IntRelType eq){
	Gecode::IntRelType g = Gecode::IRT_EQ;
	switch (eq) {
		case Gecode::IRT_EQ:
			g = Gecode::IRT_NQ; break;
		case Gecode::IRT_NQ:
			g = Gecode::IRT_EQ; break;
		case Gecode::IRT_LQ:
			g = Gecode::IRT_GR; break;
		case Gecode::IRT_GQ:
			g = Gecode::IRT_LE; break;
		case Gecode::IRT_LE:
			g = Gecode::IRT_GQ; break;
		case Gecode::IRT_GR:
			g = Gecode::IRT_LQ; break;
	}
	return g;
}

Gecode::IntRelType CP::toRelType(MINISAT::EqType eq){
	Gecode::IntRelType g = Gecode::IRT_EQ;
	switch (eq) {
		case MINISAT::MEQ:
			g =  Gecode::IRT_EQ; break;
		case MINISAT::MNEQ:
			g =  Gecode::IRT_NQ; break;
		case MINISAT::MLEQ:
			g =  Gecode::IRT_LQ; break;
		case MINISAT::MGEQ:
			g =  Gecode::IRT_GQ; break;
		case MINISAT::ML:
			g =  Gecode::IRT_LE; break;
		case MINISAT::MG:
			g =  Gecode::IRT_GR; break;
	}
	return g;
}
