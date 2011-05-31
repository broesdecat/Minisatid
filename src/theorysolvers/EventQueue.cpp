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
	event2propagator[PRINTSTATE];
	event2propagator[PRINTSTATS];
	event2propagator[CHOICE];
	event2propagator[COMPLETEMODEL];
	event2propagator[DECISIONLEVEL];
	event2propagator[BACKTRACK];
}

EventQueue::~EventQueue() {
	deleteList<Propagator>(allpropagators);
}

void EventQueue::notifyVarAdded(){
	while(litevent2propagator.size()<2*getPCSolver().nVars()){
		map<PRIORITY, vector<Propagator*> > newmap;
		newmap[FAST];
		newmap[SLOW];
		litevent2propagator.push_back(newmap);
	}
}

void EventQueue::setTrue(const Lit& l){
	const map<PRIORITY, vector<Propagator*> >& listbypriority = litevent2propagator[toInt(l)];
	for(std::vector<Propagator*>::const_iterator i=listbypriority.at(FAST).begin(); i<listbypriority.at(FAST).end(); ++i){
		if(!(*i)->isQueued()){
			(*i)->notifyQueued();
			fastqueue.push(*i);
		}
	}
	for(std::vector<Propagator*>::const_iterator i=listbypriority.at(SLOW).begin(); i<listbypriority.at(SLOW).end(); ++i){
		if(!(*i)->isQueued()){
			(*i)->notifyQueued();
			slowqueue.push(*i);
		}
	}
}

void EventQueue::finishParsing(bool& unsat){
	unsat = false;

	for(std::vector<Propagator*>::const_iterator i=earlyfinishparsing.begin(); !unsat && i<earlyfinishparsing.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			//TODO propagator can be deleted (but then need to update all relevant datastructures)
		}
	}
	for(std::vector<Propagator*>::const_iterator i=latefinishparsing.begin(); !unsat && i<latefinishparsing.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			//TODO propagator can be deleted (but then need to update all relevant datastructures)
		}
	}

	// Do all possible propagations that are queued
	if (notifyPropagate() != nullPtrClause) {
		unsat = true; return;
	}
}

rClause EventQueue::notifyPropagate(){
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
		p->notifyDeQueued();
		confl = p->notifypropagate();
	}
	return confl;
}

rClause EventQueue::notifyFullAssignmentFound(){
	rClause confl = nullPtrClause;
	for(std::vector<Propagator*>::const_iterator i=event2propagator.at(COMPLETEMODEL).begin(); confl==nullPtrClause && i<event2propagator.at(COMPLETEMODEL).end(); ++i){
		confl = (*i)->notifyFullAssignmentFound();
	}
	return confl;
}

void EventQueue::notifyNewDecisionLevel(){
	for(std::vector<Propagator*>::const_iterator i=event2propagator.at(DECISIONLEVEL).begin(); i<event2propagator.at(DECISIONLEVEL).end(); ++i){
		(*i)->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel){
	for(std::vector<Propagator*>::const_iterator i=event2propagator.at(BACKTRACK).begin(); i<event2propagator.at(BACKTRACK).end(); ++i){
		(*i)->notifyBacktrack(untillevel);
	}
}

Var EventQueue::notifyBranchChoice(Var var){
	Var currentvar = var;
	for(std::vector<Propagator*>::const_iterator i=event2propagator.at(CHOICE).begin(); i<event2propagator.at(CHOICE).end(); ++i){
		currentvar = (*i)->notifyBranchChoice(currentvar);
	}
	return currentvar;
}

void EventQueue::printState() const {
	for(std::vector<Propagator*>::const_iterator i=event2propagator.at(PRINTSTATE).begin(); i<event2propagator.at(PRINTSTATE).end(); ++i){
		(*i)->printState();
	}
}

void EventQueue::printStatistics() const {
	for(std::vector<Propagator*>::const_iterator i=event2propagator.at(PRINTSTATS).begin(); i<event2propagator.at(PRINTSTATS).end(); ++i){
		(*i)->printStatistics();
	}
}
