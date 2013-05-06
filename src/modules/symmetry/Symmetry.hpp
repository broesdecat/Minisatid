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

// Symmetry -- a class to represent a symmetry:
class SymmetryPropagator: public Propagator {
private:
	const std::unordered_map<Lit,Lit> symmetrical; // mapping representing the symmetry
	// TODO: optimize the propagator actually making use of inverse
	const std::unordered_map<Lit,Lit> inverse; // mapping representing the inverse symmetry

	// literals whose explanations might still be propagatable
	std::vector<Lit> potentialLits;
	// index in the trail of next lit for which it is not checked its explanation can be propagated.
	// invariant: the last lit in potentialLits has an index in the trail before nextToPropagate
	int nextToPropagate;

	int canPropagate(Lit l);
	Lit getNextToPropagate();
	void getSymmetricalClause(rClause in_clause, std::vector<Lit>& out_clause);


public:
	SymmetryPropagator(PCSolver* solver, const Symmetry& sym);

	// superclass methods to be implemented by subclass
	virtual rClause getExplanation(const Lit&){
		throw idpexception("Invalid code path. Symmetry propagator uses lazy clause generaton.");
	}

	virtual void accept(ConstraintVisitor& visitor);
	virtual void notifyNewDecisionLevel(){} // NOTE: nothing must be done
	void notifyBacktrack(int untillevel, const Lit& decision); // TODO: @Broes: why is this an override instead of implementing an abstract method?

	// Requirement: if a conflict is generated during this method, it is obligatory to return a (relevant) conflict clause!
	virtual rClause notifypropagate();

	//TODO: implement more decently
	virtual int getNbOfFormulas() const {
		return 1;
	}

	Lit getSymmetrical(Lit in);

};

}

#endif /* MINISATID_SYMMETRY_HPP_ */
