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
			pcsolver(pcsolver),
			initialized(false){
	event2propagator[EV_PRINTSTATE];
	event2propagator[EV_PRINTSTATS];
	event2propagator[EV_CHOICE];
	event2propagator[EV_PROPAGATE];
	event2propagator[EV_FULLASSIGNMENT];
	event2propagator[EV_DECISIONLEVEL];
	event2propagator[EV_BACKTRACK];
	event2propagator[EV_EXITCLEANLY];
	event2propagator[EV_ADDCLAUSE];
	event2propagator[EV_SYMMETRYANALYZE];
}

EventQueue::~EventQueue() {
	for(auto i=begin(EV_EXITCLEANLY); i<end(EV_EXITCLEANLY); ++i){
		delete(*i);
	}
}

void EventQueue::notifyVarAdded(){
	while(litevent2propagator.size()<2*getPCSolver().nVars()){
		vector<proplist> newmap;
		newmap.push_back(proplist());
		newmap.push_back(proplist());
		litevent2propagator.push_back(newmap);
	}
}

void EventQueue::addEternalPropagators(){
	for(auto propagator=begin(EV_PROPAGATE); propagator<end(EV_PROPAGATE); ++propagator){
		if(!(*propagator)->isQueued()){
			(*propagator)->notifyQueued();
			fastqueue.push(*propagator);
		}
	}
}

//TODO should check doubles in another way (or prevent any from being added) (maybe a set is better than a vector)
void EventQueue::acceptLitEvent(Propagator* propagator, const Lit& litevent, PRIORITY priority){
	for(proplist::const_iterator i=litevent2propagator[toInt(litevent)][priority].begin(); i<litevent2propagator[toInt(litevent)][priority].end(); ++i){
		if((*i)==propagator){
			return;
		}
	}
	litevent2propagator[toInt(litevent)][priority].push_back(propagator);
	if(getPCSolver().value(litevent)==l_True){
		if(!propagator->isQueued()){
			propagator->notifyQueued();
			priority==FAST?fastqueue.push(propagator):slowqueue.push(propagator);
		}
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
	if(isInitialized()){
		addEternalPropagators();
	}
	setTrue(litevent2propagator[toInt(l)][FAST], fastqueue);
	setTrue(litevent2propagator[toInt(l)][SLOW], slowqueue);
}

void EventQueue::finishParsing(bool& unsat){
	unsat = false;

	for(auto i=earlyfinishparsing.begin(); !unsat && i<earlyfinishparsing.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			(*i)->notifyNotPresent();
		}
	}
	earlyfinishparsing.clear();

	for(auto i=latefinishparsing.begin(); !unsat && i<latefinishparsing.end(); ++i){
		bool present = true;
		(*i)->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, (*i)->getName(), getPCSolver().verbosity());
			(*i)->notifyNotPresent();
		}
	}
	latefinishparsing.clear();


	//IMPORTANT: the propagators which are no longer present should be deleted from EVERY datastructure that is used later on!
	for(auto i=event2propagator.begin(); i!=event2propagator.end(); ++i){
		for(proplist::iterator j=(*i).second.begin(); j<(*i).second.end(); ++j){
			if(!(*j)->isPresent()){
				j = --(*i).second.erase(j);
			}
		}
	}
	for(auto i=litevent2propagator.begin(); i<litevent2propagator.end(); ++i){
		for(vector<proplist >::iterator j=(*i).begin(); j!=(*i).end(); ++j){
			for(proplist::iterator k=(*j).begin(); k<(*j).end(); ++k){
				if(!(*k)->isPresent()){
					k = --(*j).erase(k);
				}
			}
		}
	}
	for(auto j=allpropagators.begin(); j<allpropagators.end(); ++j){
		if(!(*j)->isPresent() && !(*j)->isUsedForSearch()){
			delete(*j);
			j = --allpropagators.erase(j);
		}
	}

	notifyInitialized();
	addEternalPropagators();

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

proplist::const_iterator EventQueue::begin(EVENT event) const{
	return event2propagator.at(event).begin();
}

proplist::const_iterator EventQueue::end(EVENT event) const{
	return event2propagator.at(event).end();
}

rClause EventQueue::notifyFullAssignmentFound(){
	rClause confl = nullPtrClause;
	for(auto i=begin(EV_FULLASSIGNMENT); confl==nullPtrClause && i<end(EV_FULLASSIGNMENT); ++i){
		confl = (*i)->notifyFullAssignmentFound();
	}
	return confl;
}

void EventQueue::notifyClauseAdded(rClause clauseID){
	for(auto i=begin(EV_ADDCLAUSE); i<end(EV_ADDCLAUSE); ++i){
		(*i)->notifyClauseAdded(clauseID);
	}
}

bool EventQueue::symmetryPropagationOnAnalyze(const Lit& p){
	for(auto i=begin(EV_SYMMETRYANALYZE); i<end(EV_SYMMETRYANALYZE); ++i){
		if((*i)->symmetryPropagationOnAnalyze(p)){
			return true;
		}
	}
	return false;
}

void EventQueue::notifyNewDecisionLevel(){
	for(auto i=begin(EV_DECISIONLEVEL); i<end(EV_DECISIONLEVEL); ++i){
		(*i)->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel, const Lit& decision){
	for(auto i=begin(EV_BACKTRACK); i<end(EV_BACKTRACK); ++i){
		(*i)->notifyBacktrack(untillevel, decision);
	}
}

Var EventQueue::notifyBranchChoice(Var var){
	Var currentvar = var;
	for(auto i=begin(EV_CHOICE); i<end(EV_CHOICE); ++i){
		currentvar = (*i)->notifyBranchChoice(currentvar);
	}
	return currentvar;
}

void EventQueue::printState() const {
	for(auto i=begin(EV_PRINTSTATE); i<end(EV_PRINTSTATE); ++i){
		(*i)->printState();
	}
}

void EventQueue::printStatistics() const {
	for(auto i=begin(EV_PRINTSTATS); i<end(EV_PRINTSTATS); ++i){
		(*i)->printStatistics();
	}
}
