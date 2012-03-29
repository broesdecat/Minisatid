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
}

EventQueue::~EventQueue() {
	// TODO propagator deletion
	/*for (uint i = 0; i < size(EV_EXITCLEANLY); ++i) {
		delete (props[i]);
	}*/
	deleteList<GenWatch>(lit2watches);
}

void EventQueue::preventPropagation() {
	allowpropagation = false;
}
void EventQueue::allowPropagation() {
	allowpropagation = true;
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
			fastqueue.push(propagator);
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
			fastqueue.push(*i);
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
	for (proplist::const_iterator i = lit2priority2propagators[toInt(litevent)][priority].cbegin();
			i < lit2priority2propagators[toInt(litevent)][priority].cend(); ++i) {
		if ((*i) == propagator) {
			return;
		}
	}
	lit2priority2propagators[toInt(litevent)][priority].push_back(propagator);
	if (getPCSolver().value(litevent) == l_True) {
		if (!propagator->isQueued()) {
			propagator->notifyQueued();
			priority == FAST ? fastqueue.push(propagator) : slowqueue.push(propagator);
		}
	}
}

// TODO turn lits into litwatches and add accepted flag?
void EventQueue::accept(GenWatch* const watch) {
// TODO commented this for lazy grounding, check issues with aggregates?
//	if (not getPCSolver().isDecisionVar(var(watch->getPropLit()))) {
//		getPCSolver().notifyDecisionVar(var(watch->getPropLit()));
//	}
	bool addwatch = true;
	if (getPCSolver().value(watch->getPropLit()) == l_True) { // FIXME should happen in all add methods?
		// are propagated asap, but not in this method as that leads to correctness issues
		// TODO how to handle those better?
		propagateasap.push_back(watch);
		if (watch->dynamic()) {
			addwatch = false;
		}
	}
	if (addwatch) {
		lit2watches[toInt(watch->getPropLit())].push_back(watch);
	}
}

void EventQueue::setTrue(const proplist& list, queue<Propagator*>& queue) {
	const unsigned int size = list.size();
	for (unsigned int i = 0; i < size; ++i) {
		Propagator* p = list[i];
		if (!p->isQueued()) {
			p->notifyQueued();
			queue.push(p);
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

void EventQueue::acceptFinishParsing(Propagator* propagator, bool late) {
	if (late) {
		finishparsing.push_back(propagator);
	} else {
		finishparsing.push_front(propagator);
	}
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

void EventQueue::finishParsing() {
	MAssert(not isUnsat());

	if (finishing || not allowpropagation || finishparsing.size() == 0) {
		return;
	}
	finishing = true;

	if (getPCSolver().verbosity() > 1) {
		clog << ">>> Adding additional constraints to search\n";
	}

	while (finishparsing.size() > 0 && not isUnsat()) {
		while (finishparsing.size() > 0 && not isUnsat()) {
			auto prop = finishparsing.front();
			finishparsing.pop_front();
			bool present = true;
			//FIXME prop->finishParsing(present);
			if (isUnsat()) {
				break;
			}
			if (!present) {
				printNoPropagationsOn(clog, prop->getName(), getPCSolver().verbosity());
				prop->notifyNotPresent();
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
					fastqueue.push(*prop);
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

rClause EventQueue::checkDecidables() {
	rClause confl = nullPtrClause;
	while (not propagatedecidables.empty() && confl == nullPtrClause) {
		auto prop = propagatedecidables.front();
		propagatedecidables.pop();
		confl = prop->notifypropagate();
	}
	return confl;
}

rClause EventQueue::notifyPropagate() {
	if (not allowpropagation) {
		return nullPtrClause;
	}

	rClause confl = nullPtrClause;
	confl = checkDecidables();

	for (auto i = propagateasap.cbegin(); i < propagateasap.cend() && confl == nullPtrClause; ++i) {
		confl = checkDecidables();
		if (confl != nullPtrClause) {
			break;
		}

		(*i)->propagate();
	}
	propagateasap.clear();

	assert(getPCSolver().satState()!=SATVAL::UNSAT);
	while (fastqueue.size() + slowqueue.size() != 0 && confl == nullPtrClause) {
		MAssert(fastqueue.size() + slowqueue.size() != 0);
		confl = checkDecidables();
		if (confl != nullPtrClause || fastqueue.size() + slowqueue.size() == 0) { // Might get called recursively (TODO should that be prevented?) so might be empty here
			break;
		}

		Propagator* p = NULL;
		if (fastqueue.size() != 0) {
			p = fastqueue.front();
			fastqueue.pop();
		} else {
			p = slowqueue.front();
			slowqueue.pop();
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

rClause EventQueue::notifyFullAssignmentFound() {
	//FIXME
/*	rClause confl = nullPtrClause;
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
}

void EventQueue::acceptForDecidable(Var v, Propagator* prop) {
	MAssert((uint)v<var2decidable.size());
	if (not getPCSolver().isDecisionVar(v)) {
		var2decidable[v].push_back(prop);
	} else {
		prop->notifypropagate();
	}
}

void EventQueue::notifyBecameDecidable(Var v) {
	MAssert((uint)v<var2decidable.size());
	for (auto i = var2decidable[v].cbegin(); i < var2decidable[v].cend(); ++i) {
		propagatedecidables.push(*i);
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
		backtrackqueue.pop();
	}
	auto props = event2propagator.at(EV_BACKTRACK);
	for (uint i = 0; i < size(EV_BACKTRACK); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->notifyBacktrack(untillevel, decision);
	}
}
