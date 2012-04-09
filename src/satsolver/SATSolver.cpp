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

Minisat::Solver* MinisatID::createSolver(MinisatID::PCSolver* pcsolver){
	auto s = new Minisat::Solver(pcsolver);
	auto options = pcsolver->modes();
	s->random_var_freq = options.rand_var_freq;
	s->var_decay = options.var_decay;
	s->verbosity = options.verbosity;
	s->random_seed = options.randomseed;
	s->max_learned_clauses = options.maxNbOfLearnedClauses;
	if(options.polarity==Polarity::RAND){
		s->rnd_pol=true;
	}
	return s;
}
