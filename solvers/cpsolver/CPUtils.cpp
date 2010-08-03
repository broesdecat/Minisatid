#include <solvers/cpsolver/CPUtils.hpp>

namespace CP {
	bool isTrue(Gecode::BoolVar var){
		return var.assigned() && var.in(1);
	}

	bool isFalse(Gecode::BoolVar var) {
		return var.assigned() && var.in(0);
	}

	bool isAssigned(Gecode::BoolVar var){
		return var.assigned();
	}

	Gecode::IntRelType negate(Gecode::IntRelType eq){
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

	Gecode::IntRelType toRelType(MINISAT::EqType eq){
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
}
