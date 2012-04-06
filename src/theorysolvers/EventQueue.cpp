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
#include "constraintvisitors/ConstraintVisitor.hpp"

#include "utils/PrintMessage.hpp"

#include <iostream>
#include <typeinfo>

using namespace MinisatID;
using namespace std;

EventQueue::EventQueue(PCSolver& pcsolver)
		: pcsolver(pcsolver), savingstate(false), backtrackedtoroot(false) {
	event2propagator[EV_PROPAGATE];
	event2propagator[EV_DECISIONLEVEL];
	event2propagator[EV_BACKTRACK];
	event2propagator[EV_MODELFOUND];
}

EventQueue::~EventQueue() {
	for(auto i=allpropagators.cbegin(); i<allpropagators.cend(); ++i) {
		delete(*i);
	}
	deleteList<GenWatch>(lit2watches);
}

bool EventQueue::isUnsat() const{
	return getPCSolver().satState() == SATVAL::UNSAT;
}

void EventQueue::saveState(){
	savingstate = true;
	newpropagators.clear();
	auto props = event2propagator.at(EV_STATEFUL);
	for (uint i = 0; i < size(EV_STATEFUL); ++i) {
		props[i]->saveState();
	}
}
void EventQueue::resetState(){
	for(auto i=newpropagators.cbegin(); i<newpropagators.cend(); ++i) {
		(*i)->notifyNotPresent();
	}
	newpropagators.clear();
	savingstate = false;
	auto props = event2propagator.at(EV_STATEFUL);
	for (uint i = 0; i < size(EV_STATEFUL); ++i) {
		props[i]->resetState();
	}
}

// NOTE: EACH propagator has to register here for the general methods
void EventQueue::accept(Propagator* propagator){
#ifdef DEBUG
	for(auto i=allpropagators.cbegin(); i<allpropagators.cend(); ++i){
		MAssert(propagator!=*i);
	}
#endif
	allpropagators.push_back(propagator);
	if(savingstate){
		newpropagators.push_back(propagator);
	}
}

void EventQueue::notifyNbOfVars(uint64_t nbvars){
	while (lit2priority2propagators.size() < 2 * nbvars) {
		vector<proplist> newmap;
		newmap.push_back( { });
		newmap.push_back( { });
		lit2priority2propagators.push_back(newmap);
		lit2watches.push_back( { });
	}
	var2decidable.resize(nbvars);
}

void EventQueue::addEternalPropagators() {
	auto props = event2propagator.at(EV_PROPAGATE);
	for (uint i = 0; i < size(EV_PROPAGATE); ++i) {
		auto propagator = props[i];
		if (not propagator->isQueued()) {
			propagator->notifyQueued();
			fastqueue.push_back(propagator);
		}
	}
}

void EventQueue::notifyBoundsChanged(IntVar* var) {
	for (auto i = intvarid2propagators[var->id()].cbegin(); i < intvarid2propagators[var->id()].cend(); ++i) {
		if (!(*i)->isPresent()) {
			continue;
		}
		if (not (*i)->isQueued()) {
			fastqueue.push_back(*i);
		}
	}
}

//TODO should check doubles in another way (or prevent any from being added) (maybe a set is better than a vector)
void EventQueue::accept(Propagator* propagator, const Lit& litevent, PRIORITY priority) {
	if (not getPCSolver().isDecisionVar(var(litevent))) {
		getPCSolver().notifyDecisionVar(var(litevent));
	}
//TODO if a residual is watched, do something in the propagator
//do not forget other accepts and the sat solver watches (separate!)
	auto& list = lit2priority2propagators[toInt(litevent)][priority]; // TODO speed up by making it a set?
	for (auto i = list.cbegin(); i < list.cend(); ++i) {
		if ((*i) == propagator) {
			return;
		}
	}
	list.push_back(propagator);
	if (getPCSolver().value(litevent) == l_True && not propagator->isQueued()) {
		propagator->notifyQueued();
		priority == FAST ? fastqueue.push_back(propagator) : slowqueue.push_back(propagator);
	}
}

// TODO turn lits into litwatches and add accepted flag?
void EventQueue::accept(GenWatch* const watch) {
// TODO commented following for lazy grounding, check issues with aggregates?
	if (not getPCSolver().isDecisionVar(var(watch->getPropLit()))) {
		getPCSolver().notifyDecisionVar(var(watch->getPropLit()));
	}
	bool addwatch = true;
	if (getPCSolver().value(watch->getPropLit()) == l_True) { // FIXME should happen in all add methods?
		// are propagated asap, but not in this method as that leads to correctness issues
		// TODO how to handle those better?
		propagatewatchesasap.push_back(watch);
		if (watch->dynamic()) {
			addwatch = false;
		}
	}
	if (addwatch) {
		lit2watches[toInt(watch->getPropLit())].push_back(watch);
	}
}

void EventQueue::setTrue(const proplist& list, deque<Propagator*>& queue) {
	for (unsigned int i = 0; i < list.size(); ++i) {
		auto p = list[i];
		if (!p->isQueued()) {
			p->notifyQueued();
			queue.push_back(p);
		}
	}
}

void EventQueue::setTrue(const Lit& l) {
	addEternalPropagators();
	for (uint i = 0; i != lit2watches[toInt(l)].size(); ++i) {
		lit2watches[toInt(l)][i]->propagate();
	}
	// TODO should be sped up a lot
	watchlist remwatches;
	for (auto i = lit2watches[toInt(l)].cbegin(); i != lit2watches[toInt(l)].cend(); ++i) {
		if (not (*i)->dynamic()) {
			remwatches.push_back(*i);
		}
	}
	lit2watches[toInt(l)] = remwatches;
	setTrue(lit2priority2propagators[toInt(l)][FAST], fastqueue);
	setTrue(lit2priority2propagators[toInt(l)][SLOW], slowqueue);
}

rClause EventQueue::notifyFullAssignmentFound(){
	auto confl = nullPtrClause;
	for(auto i=event2propagator[EV_MODELFOUND].cbegin(); confl==nullPtrClause && i<event2propagator[EV_MODELFOUND].cend(); ++i) {
		confl = (*i)->notifyFullAssignmentFound();
	}
	return confl;
}

// TODO check cost of this method
void EventQueue::clearNotPresentPropagators() {
	//IMPORTANT: the propagators which are no longer present should be deleted from EVERY datastructure that is used later on!
	for (auto i = lit2priority2propagators.begin(); i < lit2priority2propagators.end(); ++i) {
		for (auto j = (*i).begin(); j != (*i).end(); ++j) {
			auto temp = *j;
			j->clear();
			for (auto k = temp.cbegin(); k < temp.cend(); ++k) {
				if ((*k)->isPresent()) {
					j->push_back(*k);
				}
			}
		}
	}

	for (auto i = intvarid2propagators.begin(); i != intvarid2propagators.end(); ++i) {
		auto temp = *i;
		i->clear();
		for (auto prop = temp.cbegin(); prop != temp.cend(); ++prop) {
			if ((*prop)->isPresent()) {
				i->push_back(*prop);
			}
		}
	}

	for (auto i = event2propagator.begin(); i != event2propagator.end(); ++i) {
		auto temp = i->second;
		i->second.clear();
		for (auto prop = temp.cbegin(); prop != temp.cend();) {
			if ((*prop)->isPresent()) {
				i->second.push_back(*prop);
			}
		}
	}

	auto temp = newpropagators;
	newpropagators.clear();
	for(auto prop=temp.cbegin(); prop<temp.cend(); ++prop) {
		if((*prop)->isPresent()){
			newpropagators.push_back(*prop);
		}
	}

	for (auto j = allpropagators.begin(); j < allpropagators.end();) {
		if (not (*j)->isPresent()) {
			delete (*j);
			j = allpropagators.erase(j);
		} else {
			++j;
		}
	}
}

rClause EventQueue::notifyPropagate() {
	auto confl = nullPtrClause;

	for (auto i = propagatewatchesasap.cbegin(); i < propagatewatchesasap.cend() && confl == nullPtrClause; ++i) {
		(*i)->propagate();
	}
	propagatewatchesasap.clear();

	addEternalPropagators();

	MAssert(getPCSolver().satState()!=SATVAL::UNSAT);
	while (fastqueue.size() + slowqueue.size() != 0 && confl == nullPtrClause) {
		MAssert(fastqueue.size() + slowqueue.size() != 0);
		if (confl != nullPtrClause || fastqueue.size() + slowqueue.size() == 0) { // Might get called recursively (TODO should that be prevented?) so might be empty here
			break;
		}

		Propagator* p = NULL;
		if (fastqueue.size() != 0) {
			p = fastqueue.front();
			fastqueue.pop_front();
		} else {
			p = slowqueue.front();
			slowqueue.pop_front();
		}
		p->notifyDeQueued();
		confl = p->notifypropagate();
		MAssert(getPCSolver().satState()!=SATVAL::UNSAT || confl!=nullPtrClause);
	}

	return confl;
}

void EventQueue::accept(ConstraintVisitor& visitor){
	for (auto i = allpropagators.cbegin(); i < allpropagators.cend(); ++i) {
		(*i)->accept(visitor);
	}
}

uint EventQueue::size(EVENT event) const {
	return event2propagator.at(event).size();
}

void EventQueue::acceptForDecidable(Var v, Propagator* prop) {
	MAssert((uint)v<var2decidable.size());
	if (not getPCSolver().isDecisionVar(v)) {
		var2decidable[v].push_back(prop);
	} else {
		fastqueue.push_back(prop);
	}
}

void EventQueue::notifyBecameDecidable(Var v) {
	MAssert((uint)v<var2decidable.size());
	for (auto i = var2decidable[v].cbegin(); i < var2decidable[v].cend(); ++i) {
		fastqueue.push_back(*i);
	}
	var2decidable[v].clear();
}

void EventQueue::notifyNewDecisionLevel() {
	if(backtrackedtoroot){
		backtrackedtoroot = false;
		//clearNotPresentPropagators(); // FIXME this turns out to be extremely expensive. WHY???
	}
	auto props = event2propagator.at(EV_DECISIONLEVEL);
	for (uint i = 0; i < size(EV_DECISIONLEVEL); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel, const Lit& decision) {
	while (not backtrackqueue.empty()) {
		backtrackqueue.front()->notifyBacktrack(untillevel, decision);
		backtrackqueue.pop_front();
	}
	auto props = event2propagator.at(EV_BACKTRACK);
	for (uint i = 0; i < size(EV_BACKTRACK); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->notifyBacktrack(untillevel, decision);
	}
	backtrackedtoroot = untillevel==0;
}
