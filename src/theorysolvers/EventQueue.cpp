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
	event2propagator[EV_REMOVECLAUSE];
	event2propagator[EV_SYMMETRYANALYZE];
}

EventQueue::~EventQueue() {
	auto props = event2propagator.at(EV_EXITCLEANLY);
	for(uint i=0; i<size(EV_EXITCLEANLY); ++i){
		delete(props[i]);
	}
	deleteList<Watch>(watchevent2propagator);
}

void EventQueue::notifyVarAdded(){
	while(litevent2propagator.size()<2*getPCSolver().nVars()){
		vector<proplist> newmap;
		newmap.push_back(proplist());
		newmap.push_back(proplist());
		litevent2propagator.push_back(newmap);
		watchevent2propagator.push_back(watchlist());
	}
}

void EventQueue::addEternalPropagators(){
	auto props = event2propagator.at(EV_PROPAGATE);
	for(uint i=0; i<size(EV_PROPAGATE); ++i){
		Propagator* propagator = props[i];
		if(!propagator->isQueued()){
			propagator->notifyQueued();
			fastqueue.push(propagator);
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

// TODO turn lits into litwatches and add accepted flag?
void EventQueue::accept(Watch* watch){
	watchevent2propagator[toInt(watch->getPropLit())].push_back(watch);
	if(getPCSolver().value(watch->getPropLit())==l_True){
		watch->propagate();
	}
}

void EventQueue::acceptFinishParsing(Propagator* propagator, bool late){
	if(late){
		latefinishparsing.push_back(propagator);
	}else{
		earlyfinishparsing.push_back(propagator);
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
	for(int i=0; i!=watchevent2propagator[toInt(l)].size(); ++i){
		watchevent2propagator[toInt(l)][i]->propagate();
	}
	setTrue(litevent2propagator[toInt(l)][FAST], fastqueue);
	setTrue(litevent2propagator[toInt(l)][SLOW], slowqueue);
}

void EventQueue::finishParsing(bool& unsat){
	unsat = false;

	for(int i=0; !unsat && i!=earlyfinishparsing.size(); ++i){
		Propagator* prop = earlyfinishparsing[i];
		bool present = true;
		prop->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, prop->getName(), getPCSolver().verbosity());
			prop->notifyNotPresent();
		}
	}
	earlyfinishparsing.clear();

	for(int i=0; !unsat && i!=latefinishparsing.size(); ++i){
		Propagator* prop = latefinishparsing[i];
		bool present = true;
		prop->finishParsing(present, unsat);
		if(!present){
			printNoPropagationsOn(clog, prop->getName(), getPCSolver().verbosity());
			prop->notifyNotPresent();
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

uint EventQueue::size(EVENT event) const{
	return event2propagator.at(event).size();
}

rClause EventQueue::notifyFullAssignmentFound(){
	rClause confl = nullPtrClause;
	auto props = event2propagator.at(EV_FULLASSIGNMENT);
	for(uint i=0; confl==nullPtrClause && i<size(EV_FULLASSIGNMENT); ++i){
		if(!props[i]->isPresent()){ continue; }
		confl = props[i]->notifyFullAssignmentFound();
	}
	return confl;
}

void EventQueue::notifyClauseAdded(rClause clauseID){
	auto props = event2propagator.at(EV_ADDCLAUSE);
	for(uint i=0; i<size(EV_ADDCLAUSE); ++i){
		if(!props[i]->isPresent()){ continue; }
		props[i]->notifyClauseAdded(clauseID);
	}
}

void EventQueue::notifyClauseDeleted(rClause clauseID){
	auto props = event2propagator.at(EV_REMOVECLAUSE);
	for(uint i=0; i<size(EV_REMOVECLAUSE); ++i){
		if(!props[i]->isPresent()){ continue; }
		props[i]->notifyClauseAdded(clauseID);
	}
}

bool EventQueue::symmetryPropagationOnAnalyze(const Lit& p){
	auto props = event2propagator.at(EV_SYMMETRYANALYZE);
	for(uint i=0; i<size(EV_SYMMETRYANALYZE); ++i){
		if(!props[i]->isPresent()){ continue; }
		if(props[i]->symmetryPropagationOnAnalyze(p)){
			return true;
		}
	}
	return false;
}

void EventQueue::notifyNewDecisionLevel(){
	auto props = event2propagator.at(EV_DECISIONLEVEL);
	for(uint i=0; i<size(EV_DECISIONLEVEL); ++i){
		if(!props[i]->isPresent()){ continue; }
		props[i]->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel, const Lit& decision){
	while(not backtrackqueue.empty()){
		backtrackqueue.front()->notifyBacktrack(untillevel, decision);
		backtrackqueue.pop();
	}
	auto props = event2propagator.at(EV_BACKTRACK);
	for(uint i=0; i<size(EV_BACKTRACK); ++i){
		if(!props[i]->isPresent()){ continue; }
		props[i]->notifyBacktrack(untillevel, decision);
	}
}

Var EventQueue::notifyBranchChoice(Var var){
	auto props = event2propagator.at(EV_CHOICE);
	Var currentvar = var;
	for(uint i=0; i<size(EV_CHOICE); ++i){
		if(!props[i]->isPresent()){ continue; }
		currentvar = props[i]->notifyBranchChoice(currentvar);
	}
	return currentvar;
}

void EventQueue::printState() const {
	auto props = event2propagator.at(EV_PRINTSTATE);
	for(uint i=0; i<size(EV_PRINTSTATE); ++i){
		if(!props[i]->isPresent()){ continue; }
		props[i]->printState();
	}
}

void EventQueue::printStatistics() const {
	auto props = event2propagator.at(EV_PRINTSTATS);
	for(uint i=0; i<size(EV_PRINTSTATS); ++i){
		if(!props[i]->isPresent()){ continue; }
		props[i]->printStatistics();
	}
}

void EventQueue::notifyBoundsChanged(IntVar* var) {
	for(auto i=intvar2propagator[var->id()].begin(); i<intvar2propagator[var->id()].end(); ++i){
		if(!(*i)->isPresent()){ continue; }
		if(not (*i)->isQueued()){
			fastqueue.push(*i);
		}
	}
}
