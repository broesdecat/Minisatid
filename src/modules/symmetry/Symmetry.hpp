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

class PCSolver;

class SymmetryData {
private:
	Symmetry sym, inverse; // Maps a literal, by its numeric equiv, to its sym/inverse literal.
public:
	SymmetryData(int nVars, const Symmetry& symmetry);

	Lit getSymmetrical(const Lit& lit) const {
		return sym.symmetry.at(lit);
	}

	Lit getInverse(const Lit& lit) const {
		return inverse.symmetry.at(lit);
	}

	const std::map<Lit, Lit>& getSymmetryMap() const {
		return sym.symmetry;
	}
};

// Symmetry -- a class to represent a symmetry:
class SymmetryPropagator: public Propagator {
private:
	const SymmetryData symmetry;
	std::vector<Lit> notifiedLits;
	int amountNeededForActive, nextToPropagate;
	Lit reasonOfPermInactive;

	std::vector<Lit> activityTrail;
	std::vector<int> amountNeededTrail;
	std::vector<std::vector<Lit> > notifiedLitTrail;

public:
	SymmetryPropagator(PCSolver* solver, const Symmetry& sym);

	// Propagator methods
	virtual void 	accept(ConstraintVisitor& visitor){ throw notYetImplemented("Accept"); }
	virtual rClause getExplanation(const Lit&) { throw idpexception("Error, invalid code path."); }
	// Checks presence of aggregates and initializes all counters. UNSAT is set to true if unsat is detected
	// PRESENT is set to true if aggregate propagations should be done
	virtual void notifyNewDecisionLevel();
	virtual void notifyBacktrack(int untillevel, const Lit& decision);
	virtual rClause notifypropagate();

private:
	bool addPropagationClauses() const {
		return true;
	}
	bool addConflictClauses() const {
		return true;
	}
	bool useVarOrderOptimization() const {
		return false; // TODO is this always on?
	}
	Lit getSymmetrical(const Lit& l) const {
		return symmetry.getSymmetrical(l);
	}

	Lit getInverse(const Lit& l) const {
		return symmetry.getInverse(l);
	}

	Lit getNextToPropagate();

	void notifyEnqueued(const Lit& p);

	bool canPropagate(Lit l);

	bool isActive();

	bool isPermanentlyInactive();

	bool useInactivePropagationOptimization() const { // See notifyPropagate for info
		return false;
	}

	void print();

	bool getSymmetricalClause(std::vector<Lit>& in_clause, std::vector<Lit>& out_clause);

	void getSymmetricalClause(const rClause& in_clause, std::vector<Lit>& out_clause);

	//	@pre:	in_clause is clause without true literals
	//	@post: 	out_clause is one of three options, depending on the number of unknown literals:
	//			all false literals with first most recent and second second recent
	//			first literal unknown, rest false and second most recent
	//			first two literals unknown
	void getSortedSymmetricalClause(const rClause& in_clause, std::vector<Lit>& out_clause);

	rClause propagateSymmetrical(const Lit& l);

	//CRef 	propagateSymmetrical(Symmetry* sym, Lit l);
	//bool 	hasLowerLevel(Lit first, Lit second){ return level(var(first))<level(var(second)); }
	//bool 	canPropagate(Symmetry* sym, Clause& cl);

	void testSymmetry();
	void testActivityForSymmetries();
	bool testIsActive(const std::vector<Lit>& trail);
	bool testIsPermanentlyInactive(const std::vector<Lit>& trail);
};

}

#endif /* MINISATID_SYMMETRY_HPP_ */
