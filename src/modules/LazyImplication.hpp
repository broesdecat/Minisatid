/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

class PCSolver;
class Watch;

class LazyTseitinClause: public Propagator {
private:
	static int ltcids;
	int ltcid;
	int clauseID; // The reference the grounder can use to identify this lazy clause
	LazyGrounder* monitor; // To request additional grounding

	ImplicationType type;
	Implication implone; // Represents IMPLIES:  head => body  (only if type==EQ or type==Implies)
	Implication impltwo; // Represents IMPLIEDBY: ~head => ~body (only if type==EQ or type==Impliedby)

	litlist newgrounding; // Used to temporarily store newly grounded literals (created during the same method which will consume them)

	bool alreadypropagating; // To prevent recursion
	bool impliesfired, impliedbyfired;

public:
	LazyTseitinClause(PCSolver* engine, const Implication& impl, LazyGrounder* monitor, int clauseID);

	void addGrounding(const litlist& list);

	void fired(bool implies) {
		if (implies) {
			impliesfired = true;
		} else {
			impliedbyfired = true;
		}
	}

	virtual rClause notifypropagate();

	virtual void accept(ConstraintVisitor& visitor);

	virtual rClause getExplanation(const Lit&) {
		throw idpexception("Invalid code path");
	}
	virtual void notifyNewDecisionLevel() {
		throw idpexception("Invalid code path");
	}
	virtual void notifyBacktrack(int, const Lit&) {
		throw idpexception("Invalid code path");
	}

	virtual int getNbOfFormulas() const {
		auto size = 0;
		if (hasImplies()) {
			size += implone.conjunction ? implone.body.size() : 1;
		}
		if (hasImpliedBy()) {
			size += impltwo.conjunction ? 1 : impltwo.body.size();
		}
		return size;
	}

private:
	bool checkPropagation(Implication& tocheck, bool signswapped, Implication& complement, bool& grounded);

	bool isEquivalence() const {
		return type == ImplicationType::EQUIVALENT;
	}

	bool hasImplies() const {
		return isEquivalence() || type == ImplicationType::IMPLIES;
	}

	bool hasImpliedBy() const {
		return isEquivalence() || type == ImplicationType::IMPLIEDBY;
	}
};
}
