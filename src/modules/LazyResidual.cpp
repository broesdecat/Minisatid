/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/LazyResidual.hpp"
#include <iostream>
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace std;
using namespace MinisatID;

// Watch BOTH: so watching when it becomes decidable
LazyResidual::LazyResidual(PCSolver* engine, Atom var, Value watchedvalue, LazyGroundingCommand* monitor)
		: 	Propagator(engine, "lazy residual notifier"),
			monitor(monitor),
			residual(var),
			watchedvalue(watchedvalue) {
	getPCSolver().accept(this);

	switch (watchedvalue) {
	case Value::True:
		if (engine->modes().expandimmediately && value(mkPosLit(var)) != l_False) {
			getPCSolver().acceptForPropagation(this);
			return;
		}
		getPCSolver().accept(this, mkPosLit(var), PRIORITY::FAST);
		break;
	case Value::False:
		if (engine->modes().expandimmediately && value(mkPosLit(var)) != l_True) {
			getPCSolver().acceptForPropagation(this);
			return;
		}
		getPCSolver().accept(this, mkNegLit(var), PRIORITY::FAST);
		break;
	case Value::Unknown:
		if (engine->modes().expandimmediately) {
			getPCSolver().acceptForPropagation(this);
			return;
		}
		getPCSolver().acceptForDecidable(var, this);
		break;
	}
}

void LazyResidual::accept(ConstraintVisitor& visitor) {
	visitor.add(LazyGroundLit(residual, watchedvalue, monitor));
}

rClause LazyResidual::notifypropagate() {
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	// NOTE: have to make sure that constraints are never added at a level where they will not have full effect!
	auto confl = nullPtrClause;
	if (not modes().expandimmediately) {
		switch (watchedvalue) {
		case Value::Unknown:
			if (not getPCSolver().isDecisionVar(residual)) {
				return confl;
			}
			break;
		case Value::False:
			if (getPCSolver().value(mkPosLit(residual)) != l_False) {
				return confl;
			}
			break;
		case Value::True:
			if (getPCSolver().value(mkPosLit(residual)) != l_True) {
				return confl;
			}
			break;
		}
	}
	if (verbosity() > 7) {
		clog << "Firing lazy residual " << toString(residual) << " for watched value " << watchedvalue << "\n";
	}
	getPCSolver().notifyGroundingCall();
	monitor->requestGrounding(watchedvalue);

	getPCSolver().notifyFinishParsingNeed();
	notifyNotPresent();

	if (getPCSolver().isUnsat()) {
		confl = getPCSolver().createClause(Disjunction({ }), true);
	}
	return confl;
}
