#ifndef CPUTILS_H
#define CPUTILS_H

#include <gecode/int.hh>
#include <solvers/ExternalUtils.hpp>

namespace CP {
	IntRelType negate(IntRelType eq){
		IntRelType g;
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

	IntRelType toRelType(MINISAT::EqType eq){
		IntRelType g;
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
}

#endif /*CPUTILS_H*/
