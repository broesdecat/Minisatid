/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "Symmetry.hpp"

#include "satsolver/SATSolver.hpp"
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

SymmetryData::SymmetryData(const Symmetry& symmetry)
		: symm(symmetry) {
}

SymmetryPropagator::SymmetryPropagator(PCSolver* solver, const Symmetry& sym)
		: 	Propagator(DEFAULTCONSTRID, solver, "symmetry propagator"),
			symmetry(sym) {

	/*
	 getPCSolver().accept(this);
	 getPCSolver().accept(this, EV_BACKTRACK);
	 getPCSolver().accept(this, EV_DECISIONLEVEL);
	 */
}

rClause SymmetryPropagator::getExplanation(const Lit&) {
	// TODO: implement
	return getPCSolver().createClause(Disjunction(0, std::vector<Lit>()), true);
}

void SymmetryPropagator::accept(ConstraintVisitor& visitor) {
	// TODO: implement
}

void SymmetryPropagator::notifyNewDecisionLevel() {
	// TODO: implement
}

rClause SymmetryPropagator::notifypropagate() {
	// TODO: implement
	return getPCSolver().createClause(Disjunction(0, std::vector<Lit>()), true);
}

