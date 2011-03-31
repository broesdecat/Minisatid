//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#include <solvers/cpsolver/CPUtils.hpp>

namespace CP {
	bool isTrue(Gecode::BoolVar var){
		return var.assigned() && var.one();
	}

	bool isFalse(Gecode::BoolVar var) {
		return var.assigned() && var.zero();
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
