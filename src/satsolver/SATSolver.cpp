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

#include "satsolver/SATSolver.hpp"
#include "utils/Utils.hpp"

using namespace MinisatID;

#ifdef USEMINISAT22
Minisat::Solver* MinisatID::createSolver(MinisatID::PCSolver* pcsolver){
	Minisat::Solver* s = new Minisat::Solver(pcsolver);
	const SolverOption& options = pcsolver->modes();
	s->random_var_freq = options.rand_var_freq;
	s->var_decay = options.var_decay;
	s->verbosity = options.verbosity;
	return s;
}
#else
Minisat::Solver* MinisatID::createSolver(MinisatID::PCSolver* pcsolver){
	Minisat::Solver* s = new Minisat::Solver(pcsolver);
	const SolverOption& options = pcsolver->modes();
	s->random_var_freq = options.rand_var_freq;
	s->var_decay = options.var_decay;
	switch(options.polarity){
		case POL_TRUE: s->polarity_mode = 0; break;
		case POL_FALSE: s->polarity_mode = 1; break;
		case POL_STORED: s->polarity_mode = 2; break;
		case POL_RAND: s->polarity_mode = 3; break;
	}

	s->verbosity = options.verbosity;
	return s;
}
#endif