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

class LazyResidual;

class LazyResidual: public Propagator {
private:
	LazyGroundingCommand* monitor;
	Atom residual;
	Value watchedvalue;

public:
	LazyResidual(PCSolver* engine, Atom var, Value watchedvalue, LazyGroundingCommand* monitor);

	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause getExplanation(const Lit&) {
		MAssert(false);
		return nullPtrClause;
	}
	virtual void notifyNewDecisionLevel() {
		MAssert(false);
	}
	virtual void notifyBacktrack(int, const Lit&) {
		MAssert(false);
	}
	virtual int getNbOfFormulas() const {
		return 1;
	}
};
}
