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
#include "satsolver/SATSolver.hpp"

#include "utils/PrintMessage.hpp"

#include <iostream>

using namespace MinisatID;
using namespace std;

EventQueue::EventQueue(PCSolver& pcsolver):
			pcsolver(pcsolver){
	event2propagator[PRINTSTATE];
	event2propagator[PRINTSTATS];
	event2propagator[CHOICE];
	event2propagator[FULLASSIGNMENT];
	event2propagator[DECISIONLEVEL];
	event2propagator[BACKTRACK];
}

EventQueue::~EventQueue() {
	deleteList<Propagator>(allpropagators);
}

void EventQueue::notifyVarAdded(){
	while(litevent2propagator.size()<2*getPCSolver().nVars()){
		vector<proplist> newmap;
		newmap.push_back(proplist());
		newmap.push_back(proplist());
		litevent2propagator.push_back(newmap);
	}
}

void EventQueue::setTrue(const proplist& list, queue<Propagator*>& queue){
	const unsigned int size = list.size();
	for(unsigned int i=0; i<size; ++i){
		Propagator* p = list[i];
		if(!p->isQueued()){
			p->notifyQueued();
			queue.push(p);
		}
	}
}

void EventQueue::setTrue(const Lit& l){
	setTrue(litevent2propagator[toInt(l)][FAST], fastqueue);
	setTrue(litevent2propagator[toInt(l)][SLOW], slowqueue);
}

void EventQueue::finishParsing(bool& unsat){
	unsat = false;

	//FIXME remember all !present and go over them and all data structs afterwards
	proplist toberemoved;
	for(proplist::const_iterator i=earlyfinishparsing.begin(); !unsat && i<earlyfinishparsing.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			(*i)->notifyNotPresent();
		}
	}
	earlyfinishparsing.clear();

	for(proplist::const_iterator i=latefinishparsing.begin(); !unsat && i<latefinishparsing.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			(*i)->notifyNotPresent();
		}
	}
	latefinishparsing.clear();

	//IMPORTANT: the propagators which are no longer present should be deleted from EVERY datastructure that is used later on!
	for(map<EVENT, proplist >::iterator i=event2propagator.begin(); i!=event2propagator.end(); ++i){
		for(proplist::iterator j=(*i).second.begin(); j<(*i).second.end(); ++j){
			if(!(*j)->isPresent()){
				j = --(*i).second.erase(j);
			}
		}
	}
	for(vector<vector<proplist > >::iterator i=litevent2propagator.begin(); i<litevent2propagator.end(); ++i){
		for(vector<proplist >::iterator j=(*i).begin(); j!=(*i).end(); ++j){
			for(proplist::iterator k=(*j).begin(); k<(*j).end(); ++k){
				if(!(*k)->isPresent()){
					k = --(*j).erase(k);
				}
			}
		}
	}
	for(proplist::iterator j=allpropagators.begin(); j<allpropagators.end(); ++j){
		if(!(*j)->isPresent() && !(*j)->isUsedForSearch()){
			delete(*j);
			j = --allpropagators.erase(j);
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

int	EventQueue::getNbOfFormulas() const{
	int count = 0;
	for(proplist::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
		if((*i)->isPresent()){
			count += (*i)->getNbOfFormulas();
		}
	}
	return count;
}

rClause EventQueue::notifyFullAssignmentFound(){
	rClause confl = nullPtrClause;
	for(proplist::const_iterator i=event2propagator.at(FULLASSIGNMENT).begin(); confl==nullPtrClause && i<event2propagator.at(FULLASSIGNMENT).end(); ++i){
		confl = (*i)->notifyFullAssignmentFound();
	}
	return confl;
}

void EventQueue::notifyNewDecisionLevel(){
	for(proplist::const_iterator i=event2propagator.at(DECISIONLEVEL).begin(); i<event2propagator.at(DECISIONLEVEL).end(); ++i){
		(*i)->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel){
	for(proplist::const_iterator i=event2propagator.at(BACKTRACK).begin(); i<event2propagator.at(BACKTRACK).end(); ++i){
		(*i)->notifyBacktrack(untillevel);
	}
}

Var EventQueue::notifyBranchChoice(Var var){
	Var currentvar = var;
	for(proplist::const_iterator i=event2propagator.at(CHOICE).begin(); i<event2propagator.at(CHOICE).end(); ++i){
		currentvar = (*i)->notifyBranchChoice(currentvar);
	}
	return currentvar;
}

void EventQueue::printState() const {
	for(proplist::const_iterator i=event2propagator.at(PRINTSTATE).begin(); i<event2propagator.at(PRINTSTATE).end(); ++i){
		(*i)->printState();
	}
}

void EventQueue::printStatistics() const {
	for(proplist::const_iterator i=event2propagator.at(PRINTSTATS).begin(); i<event2propagator.at(PRINTSTATS).end(); ++i){
		(*i)->printStatistics();
	}
}
