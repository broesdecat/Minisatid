/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "theorysolvers/EventQueue.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "utils/PrintMessage.hpp"

#include <iostream>

using namespace MinisatID;
using namespace std;

EventQueue::EventQueue(PCSolver& pcsolver):
			pcsolver(pcsolver){

}

EventQueue::~EventQueue() {
	//TODO who deletes the propagators?
}

void EventQueue::notifyVarAdded(){
	varevent2propagator.resize(getPCSolver().nVars(), vector<Propagator*>());

}

void EventQueue::setTrue(const Lit& l){
	//FIXME add correct elements to queues
	// TESTING HACK
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		fastqueue.push(*i);
	}

	for(std::vector<Propagator*>::const_iterator i=varevent2propagator[var(l)].begin(); i<varevent2propagator[var(l)].end(); ++i){
		fastqueue.push(*i);
	}
}

rClause EventQueue::notifyFullAssignmentFound(){
	rClause confl = nullPtrClause;
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); confl==nullPtrClause && i<allpropagators.end(); ++i){
		confl = (*i)->notifyFullAssignmentFound();
	}
	return confl;
}

bool temp = false;

//TODO put clausal propagator first, IDsolver last
void EventQueue::finishParsing(bool& unsat){
	unsat = false;

	//NOTE Both aggsolver and modsolver can add rules during their initialization, so always initialize all ID solver last!
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); !unsat && i<allpropagators.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			//TODO delete propagator in some way
		}
		if(unsat){
			return;
		}
	}

	temp = true;

	// Do all propagations that have already been done on the SAT-solver level.
	if (notifyPropagate() != nullPtrClause) {
		unsat = true; return;
	}
}

void EventQueue::notifyNewDecisionLevel(){
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		(*i)->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel){
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		(*i)->notifyBacktrack(untillevel);
	}
}

rClause EventQueue::notifyPropagate(){
	if(!temp){
		return nullPtrClause;
	}
	rClause confl = nullPtrClause;
	while(fastqueue.size()+slowqueue.size()!=0 && confl==nullPtrClause){
		Propagator* p = NULL;
		if(fastqueue.size()!=0){
			p = fastqueue.front();
			fastqueue.pop();
		}else{
			p = slowqueue.front();
			slowqueue.pop();
		}
		confl = p->notifypropagate();
	}
	return confl;
}

Var EventQueue::notifyBranchChoice(Var var){
	Var currentvar = var;
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		currentvar = (*i)->notifyBranchChoice(currentvar);
	}
	return currentvar;
}

void EventQueue::printState() const {
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		(*i)->printState();
	}
}

void EventQueue::printStatistics() const {
	for(std::vector<Propagator*>::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		(*i)->printStatistics();
	}
}
