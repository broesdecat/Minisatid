/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

/**
 * head EQUIV symbol(t1, ..., tn): tx, with t1, ..., tn, tx integer variables
 */
class LazyAtomPropagator: public Propagator {
private:
	Lit head;
	std::vector<IntView*> args;
	LazyAtomGrounder* grounder;

	int maxsize;
	std::set<std::vector<int>> grounded;

public:
	LazyAtomPropagator(PCSolver* engine, const Lit& head, const std::vector<IntView*> args, LazyAtomGrounder* grounder);

	const Lit& getHead() const {
		return head;
	}

	// Propagator methods
	virtual rClause getExplanation(const Lit&) {
		throw idpexception("Invalid code path.");
	}
	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual int getNbOfFormulas() const;
	virtual void notifyNewDecisionLevel() {
		throw idpexception("Invalid code path.");
	}
	virtual void notifyBacktrack(int, const Lit&) {
		throw idpexception("Invalid code path.");
	}
};

}
