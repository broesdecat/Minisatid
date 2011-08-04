/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/DPLLTmodule.hpp"

#include "satsolver/SATSolver.hpp"

using namespace std;
using namespace MinisatID;

void Propagator::notifyBacktrack(int untillevel, const Lit& decision){
	trailindex = getPCSolver().getSATSolver()->getTrailSize();
}

bool Propagator::hasNextProp(){
	return trailindex < getPCSolver().getSATSolver()->getTrailSize();
}

const Lit& Propagator::getNextProp(){
	return getPCSolver().getSATSolver()->getTrailElem(trailindex++);
}

void Propagator::addWatch(Var atom) {
	getPCSolver().acceptLitEvent(this, mkLit(atom, false), FAST);
	getPCSolver().acceptLitEvent(this, mkLit(atom, true), FAST);
}

void Propagator::addWatch(const Lit& lit) {
	getPCSolver().acceptLitEvent(this, lit, FAST);
}
