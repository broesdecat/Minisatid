/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "satsolver/SATSolver.hpp"
#include "theorysolvers/PCSolver.hpp"

using namespace MinisatID;

#ifdef USEMINISAT22
Minisat::Solver* MinisatID::createSolver(MinisatID::PCSolver* pcsolver){
	Minisat::Solver* s = new Minisat::Solver(pcsolver);
	const SolverOption& options = pcsolver->modes();
	s->random_var_freq = options.rand_var_freq;
	s->var_decay = options.var_decay;
	s->verbosity = options.verbosity;
	s->random_seed = options.randomseed;
	if(options.polarity==POL_RAND){
		s->rnd_pol=true;
	}
	return s;
}
#else
Minisat::Solver* MinisatID::createSolver(MinisatID::PCSolver* pcsolver){
	Minisat::Solver* s = new Minisat::Solver(pcsolver);
	const SolverOption& options = pcsolver->modes();
	s->random_var_freq = options.rand_var_freq;
	s->var_decay = options.var_decay;
	s->random_seed = options.randomseed;
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
