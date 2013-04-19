/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#ifndef MINISATID_SYMMETRY_HPP_
#define MINISATID_SYMMETRY_HPP_

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

class ConstraintVisitor;
class PCSolver;

class SymmetryData {
private:
	Symmetry symm; // Stored for convenience, could be dropped

public:
	SymmetryData(const Symmetry& symmetry);

};

// Symmetry -- a class to represent a symmetry:
class SymmetryPropagator: public Propagator {
private:
	const SymmetryData symmetry;

public:
	SymmetryPropagator(PCSolver* solver, const Symmetry& sym);

	// superclass methods to be implemented by subclass
	virtual rClause getExplanation(const Lit&);

	virtual void accept(ConstraintVisitor& visitor);
	virtual void notifyNewDecisionLevel();
	// void notifyBacktrack(int untillevel, const Lit& decision); // NOTE: call explicitly when using hasnextprop/nextprop!

	// Requirement: if a conflict is generated during this method, it is obligatory to return a (relevant) conflict clause!
	virtual rClause notifypropagate();

	//TODO: implement more decently
	virtual int getNbOfFormulas() const {
		return 1;
	}

};

}

#endif /* MINISATID_SYMMETRY_HPP_ */
