/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include "external/ExternalUtils.hpp"

namespace MinisatID{

class Agg;
class IntView;

enum class Optim {
	LIST, SUBSET, AGG, VAR
};

struct OptimStatement {
	unsigned int priority; // Lower is earlier
	Optim optim;
	std::vector<Lit> to_minimize;
	Agg* agg_to_minimize;
	IntView* var;
	bool atoptimum;

	OptimStatement(uint priority, Optim optim, litlist minim) :
			priority(priority), optim(optim), to_minimize(minim), agg_to_minimize(NULL), var(NULL), atoptimum(false) {
		MAssert(optim==Optim::LIST || optim==Optim::SUBSET);
	}
	OptimStatement(uint priority, Agg* agg) :
			priority(priority), optim(Optim::AGG), agg_to_minimize(agg), var(NULL), atoptimum(false) {

	}
	OptimStatement(uint priority, IntView* var) :
			priority(priority), optim(Optim::VAR), agg_to_minimize(NULL), var(var), atoptimum(false) {

	}
};

}
