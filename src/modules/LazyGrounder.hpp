/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef LAZYGROUNDER_HPP_
#define LAZYGROUNDER_HPP_

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

/*
 * How does it work:
 * have a vector with full clauses
 * have a vector with "grounded" clauses and an index of where we are in the full clause
 * make the grounded clauses 1-watched
 *
 * during propagate:
 * 		if a clause becomes fully false, extends its grounding until it can become true, set that as watch
 * 		if it cannot be made true any more, backtrack to the appropriate level and add the full clause to the solver
 */

namespace MinisatID{

class PCSolver;

class LazyClausePropagator: public Propagator{
private:
	bool certainlytrue;
	Lit head;
	InnerDisjunction clause;
	LazyClauseMonitor* monitor;

	void handleFullyGround();

public:
	LazyClausePropagator(PCSolver* engine, const InnerLazyClause& lz);
	virtual ~LazyClausePropagator();

	void add(const Lit& lit);

	rClause notifypropagate();

	void notifyCertainlyTrue();
	void notifyCertainlyFalse();

	// Propagator methods
	virtual const char* getName			() const 					{ return "lazyclause"; }
	virtual int		getNbOfFormulas		() const 					{ return 1; }
};
}

#endif /* LAZYGROUNDER_HPP_ */
