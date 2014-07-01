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

Minisat::Solver* MinisatID::createSolver(MinisatID::PCSolver* pcsolver, bool oneshot){
	auto options = pcsolver->modes();
	MinisatHeuristic* heur;
	if(false){
		heur = new MinisatHeuristic(options.polarity==Polarity::RAND);
	}else{
		heur = new VarMTF(8);
	}

	auto s = new Minisat::Solver(pcsolver, oneshot, heur);
	s->verbosity = options.verbosity;
	s->random_seed = options.randomseed;
	s->fullmodelcheck = options.fullmodelcheck;
	s->max_learned_clauses = options.maxNbOfLearnedClauses;
	return s;
}
