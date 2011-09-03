/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/LazyGrounder.hpp"

using namespace std;
using namespace MinisatID;

LazyResidualWatch::LazyResidualWatch(PCSolver* engine, const Lit lit, LazyGroundingCommand* monitor):
		engine(engine),
		monitor(monitor), residual(lit){
	engine->accept(this);
}

void LazyResidualWatch::propagate(){
	new LazyResidual(this);
}

const Lit& LazyResidualWatch::getPropLit() const{
	return residual;
}

LazyResidual::LazyResidual(LazyResidualWatch* const watch):Propagator(watch->engine), watch(watch){
	getPCSolver().acceptForPropagation(this);
}

rClause LazyResidual::notifypropagate(){
	if(getPCSolver().getCurrentDecisionLevel()>0){
		getPCSolver().backtrackTo(0); // FIXME extremely inefficient: should rather make sure that all the add methods
		//(e.g. clauses in the sat solver, backtrack to the appropriate level if necessary
		//      (where the constraint is not unsatisfied)).
	}
	watch->monitor->requestGrounding(); // FIXME should delete the other watch too
	notifyNotPresent(); // FIXME clean way of deleting this?
	return nullPtrClause;
}
