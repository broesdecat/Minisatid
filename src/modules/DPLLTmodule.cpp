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
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

void Propagator::notifyBacktrack(int, const Lit&){ // FIXME turn into notifyBacktrack and virtual Backtrack!
	trailindex = getPCSolver().getSATSolver()->getTrailSize();
}

bool Propagator::hasNextProp(){
	return trailindex < getPCSolver().getSATSolver()->getTrailSize();
}

const Lit& Propagator::getNextProp(){
	return getPCSolver().getSATSolver()->getTrailElem(trailindex++);
}

void Propagator::addWatch(Var atom) {
	getPCSolver().accept(this, mkPosLit(atom), FAST);
	getPCSolver().accept(this, mkNegLit(atom), FAST);
}

void Propagator::addWatch(const Lit& lit) {
	getPCSolver().accept(this, lit, FAST);
}

std::string Propagator::toString(const Lit& lit) const{
	return print(lit, getPCSolver());
}
