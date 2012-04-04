/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/LazyGrounder.hpp"
#include <iostream>
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

LazyResidualWatch::LazyResidualWatch(PCSolver* engine, const Lit& lit, LazyGroundingCommand* monitor) :
		engine(engine), monitor(monitor), residual(lit) {
	engine->accept(this);
}

void LazyResidualWatch::propagate() {
	new LazyResidual(this);
}

const Lit& LazyResidualWatch::getPropLit() const {
	return residual;
}

// Watch BOTH: so watching when it becomes decidable
LazyResidual::LazyResidual(PCSolver* engine, Var var, LazyGroundingCommand* monitor) :
		Propagator(engine, "lazy residual notifier"), monitor(monitor), residual(mkPosLit(var)) {
	getPCSolver().acceptForDecidable(var, this);
}

LazyResidual::LazyResidual(LazyResidualWatch* const watch) :
		Propagator(watch->engine, "lazy residual notifier"), monitor(watch->monitor), residual(watch->residual) {
	getPCSolver().acceptForPropagation(this);
}

rClause LazyResidual::notifypropagate() {
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	// NOTE: have to make sure that constraints are never added at a level where they will no have full effect!

	// TODO check whether preventprop is still necessary
//	getPCSolver().preventPropagation(); // NOTE: necessary for inductive definitions, as otherwise might try propagation before all rules for some head have been added.
	monitor->requestGrounding(); // FIXME should delete the other watch too
//	getPCSolver().allowPropagation();

	if (not getPCSolver().isUnsat() /* FIXME FIXME && getPCSolver().isInitialized()*/) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().finishParsing();
	}
	notifyNotPresent(); // FIXME clean way of deleting this? FIXME only do this after finishparsing as this propagated is then DELETED

	if (getPCSolver().isUnsat()) {
		Disjunction d;
		d.literals = {getPCSolver().getTrail().back()};
		return getPCSolver().createClause(d, true);
	} else {
		return nullPtrClause;
	}
}
