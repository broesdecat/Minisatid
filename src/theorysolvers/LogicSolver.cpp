/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "theorysolvers/LogicSolver.hpp"
#include "wrapper/InterfaceImpl.hpp"

using namespace MinisatID;

void LogicSolver::notifyHasMonitor() {
	hasMonitor = true;
}

bool LogicSolver::isBeingMonitored() const{
	return hasMonitor;
}

void LogicSolver::notifyMonitor(const InnerPropagation& obj){
	getParent().notifyMonitor(obj);
}

void LogicSolver::notifyMonitor(const InnerBacktrack& obj){
	getParent().notifyMonitor(obj);
}
