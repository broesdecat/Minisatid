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
		: pcsolver(pcsolver), initialized(false), finishing(false), allowpropagation(true) {
	event2propagator[EV_PROPAGATE];
	event2propagator[EV_DECISIONLEVEL];
	event2propagator[EV_BACKTRACK];
	event2propagator[EV_MODELFOUND];
	event2propagator[EV_FINISH];
}

EventQueue::~EventQueue() {
	// TODO propagator deletion
	/*for (uint i = 0; i < size(EV_EXITCLEANLY); ++i) {
		delete (props[i]);
	}*/
	deleteList<GenWatch>(lit2watches);
}

bool EventQueue::isUnsat() const{
	return getPCSolver().satState() == SATVAL::UNSAT;
}

void EventQueue::notifyVarAdded() {
	while (lit2priority2propagators.size() < 2 * getPCSolver().nVars()) {
		vector<proplist> newmap;
		newmap.push_back( { });
		newmap.push_back( { });
		lit2priority2propagators.push_back(newmap);
		lit2watches.push_back( { });
	}
	var2decidable.resize(getPCSolver().nVars());
}

void EventQueue::addEternalPropagators() {
	auto props = event2propagator.at(EV_PROPAGATE);
	for (uint i = 0; i < size(EV_PROPAGATE); ++i) {
		Propagator* propagator = props[i];
		if (!propagator->isQueued()) {
			propagator->notifyQueued();
			fastqueue.push_back(propagator);
		}
	}
}

void EventQueue::notifyBoundsChanged(IntVar* var) {
	if (!isInitialized()) { // TODO enforce by design?
		return;
	}
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
	const unsigned int size = list.size();
	for (unsigned int i = 0; i < size; ++i) {
		Propagator* p = list[i];
		if (!p->isQueued()) {
			p->notifyQueued();
			queue.push_back(p);
		}
	}
}

void EventQueue::setTrue(const Lit& l) {
	if (isInitialized()) {
		addEternalPropagators();
	}
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

void EventQueue::clearNotPresentPropagators() { // TODO restore?
	//IMPORTANT: the propagators which are no longer present should be deleted from EVERY datastructure that is used later on!
	for (auto i = event2propagator.begin(); i != event2propagator.end(); ++i) {
		for (auto j = (*i).second.begin(); j < (*i).second.end();) {
			if (!(*j)->isPresent()) {
				j = (*i).second.erase(j);
			} else {
				++j;
			}
		}
	}
	for (auto i = lit2priority2propagators.begin(); i < lit2priority2propagators.end(); ++i) {
		for (auto j = (*i).begin(); j != (*i).end(); ++j) {
			for (auto k = (*j).begin(); k < (*j).end();) {
				if (!(*k)->isPresent()) {
					k = (*j).erase(k);
				} else {
					++k;
				}
			}
		}
	}
	for (auto intvar = intvarid2propagators.begin(); intvar != intvarid2propagators.end(); ++intvar) {
		for (auto prop = intvar->begin(); prop != intvar->end();) {
			if (!(*prop)->isPresent()) {
				prop = (*intvar).erase(prop);
			} else {
				++prop;
			}
		}
	}
	for (auto j = allpropagators.begin(); j < allpropagators.end();) {
		if (!(*j)->isPresent() && !(*j)->isUsedForSearch()) {
			delete (*j);
			j = allpropagators.erase(j);
		} else {
			++j;
		}
	}
}

void EventQueue::initialize() {
	MAssert(not isUnsat());

	if (finishing || not allowpropagation || event2propagator[EV_FINISH].size() == 0) {
		return;
	}
	finishing = true;

	if (getPCSolver().verbosity() > 1) {
		clog << ">>> Adding additional constraints to search\n";
	}

	while (event2propagator[EV_FINISH].size() > 0 && not isUnsat()) {
		while (event2propagator[EV_FINISH].size() > 0 && not isUnsat()) {
			auto prop = event2propagator[EV_FINISH].front();
			event2propagator[EV_FINISH].pop_front();
			prop->initialize();
			if (isUnsat()) {
				break;
			}
			if (not prop->isPresent()) {
				printNoPropagationsOn(clog, prop->getName(), getPCSolver().verbosity());
			}
		}
		if (isUnsat()) {
			break;
		}

		//clearNotPresentPropagators() TODO very expensive??

		notifyInitialized();

		// Queue all necessary propagators
		addEternalPropagators();
		for (auto intvar = intvarid2propagators.cbegin(); intvar != intvarid2propagators.cend(); ++intvar) {
			for (auto prop = intvar->begin(); prop != intvar->end(); ++prop) {
				if (not (*prop)->isQueued()) {
					fastqueue.push_back(*prop);
				}
			}
		}

		MAssert(not isUnsat());

		// Do all possible propagations that are queued
		auto confl = notifyPropagate();
		if (confl != nullPtrClause) {
			bool conflictAtRoot = getPCSolver().getCurrentDecisionLevel()==0;
			if(not conflictAtRoot){
				conflictAtRoot = getPCSolver().handleConflict(confl);
			}
			if(conflictAtRoot){
				getPCSolver().notifyUnsat(); // TODO do something with the conflict clause?
			}
		}
	}

	finishing = false;
}

rClause EventQueue::notifyPropagate() {
	if (not allowpropagation) {
		return nullPtrClause;
	}

	rClause confl = nullPtrClause;

	for (auto i = propagatewatchesasap.cbegin(); i < propagatewatchesasap.cend() && confl == nullPtrClause; ++i) {
		(*i)->propagate();
	}
	propagatewatchesasap.clear();

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

//rClause EventQueue::notifyFullAssignmentFound() {
	// FIXME
	/*auto confl = nullPtrClause;
	MAssert(getPCSolver().hasTotalModel());
	auto props = event2propagator.at(EV_FULLASSIGNMENT);
	// FIXME propagation can backtrack and invalidate total model, so should stop then!
	MAssert(getPCSolver().satState()!=SATVAL::UNSAT);
	for (uint i = 0; confl == nullPtrClause && i < size(EV_FULLASSIGNMENT) && getPCSolver().hasTotalModel(); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		confl = props[i]->notifyFullAssignmentFound();
		MAssert(getPCSolver().satState()!=SATVAL::UNSAT || confl!=nullPtrClause);
	}
	return confl;*/
//}

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
}
