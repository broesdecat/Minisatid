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
	std::map<Lit, Lit> sym, inverse; // Maps a literal, by its numeric equiv, to its sym/inverse literal.
public:
	SymmetryData(const Symmetry& symmetry);

	Lit getSymmetrical(const Lit& lit) const {
		if (sym.find(lit) != sym.cend()) {
			return sym.at(lit);
		}
		if (sym.find(~lit) != sym.cend()) {
			return ~sym.at(~lit);
		}
		return lit;
	}

	Lit getInverse(const Lit& lit) const {
		if (inverse.find(lit) != inverse.cend()) {
			return inverse.at(lit);
		}
		if (inverse.find(~lit) != inverse.cend()) {
			return ~inverse.at(~lit);
		}
		return lit;
	}

	const std::map<Lit, Lit>& getSymmetryMap() const {
		return sym;
	}

	const Symmetry& getSymmetry() const {
		return symm;
	}
};

// Symmetry -- a class to represent a symmetry:
class SymmetryPropagator: public Propagator {
private:
	const SymmetryData symmetry;
	std::vector<Lit> notifiedLits;
	uint amountNeededForActive, nextToPropagate;
	Lit reasonOfPermInactive;

	std::vector<Lit> activityTrail;
	std::vector<int> amountNeededTrail;
	std::vector<std::vector<Lit> > notifiedLitTrail;

public:
	SymmetryPropagator(PCSolver* solver, const Symmetry& sym);

	// Propagator methods
	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause getExplanation(const Lit&) {
		throw idpexception("Error, invalid code path.");
	} // Checks presence of aggregates and initializes all counters. UNSAT is set to true if unsat is detected
	// PRESENT is set to true if aggregate propagations should be done
	virtual void notifyNewDecisionLevel();
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause notifypropagate();
	virtual int getNbOfFormulas() const {
		return symmetry.getSymmetryMap().size();
	}

private:
	Lit getSymmetrical(const Lit& l) const {
		return symmetry.getSymmetrical(l);
	}

	Lit getInverse(const Lit& l) const {
		return symmetry.getInverse(l);
	}

	Lit getNextToPropagate();

	void notifyEnqueued(const Lit& p);

	bool isActive();

	bool isPermanentlyInactive();

	//	@pre:	in_clause is clause without true literals
	//	@post: 	out_clause is one of three options, depending on the number of unknown literals:
	//			all false literals with first most recent and second second recent
	//			first literal unknown, rest false and second most recent
	//			first two literals unknown
	void getSortedSymmetricalClause(const rClause& in_clause, std::vector<Lit>& out_clause);

	rClause propagateSymmetrical(const Lit& l);
};

}

#endif /* MINISATID_SYMMETRY_HPP_ */
