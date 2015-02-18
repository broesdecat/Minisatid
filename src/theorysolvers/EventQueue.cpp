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
#include "modules/LazyResidual.hpp"
#include "satsolver/SATSolver.hpp"
#include "external/ConstraintVisitor.hpp"

#include "utils/PrintMessage.hpp"
#include "external/utils/ContainerUtils.hpp"
#include "utils/NumericLimits.hpp"

#include <iostream>
#include <typeinfo>

using namespace MinisatID;
using namespace std;

EventQueue::EventQueue(PCSolver& pcsolver)
		: 	pcsolver(pcsolver),
			nbrestarts(0),
			backtrackedtoroot(false),
			_propagating(false),
			_backtracking(false),
			_requestedmore(false) {
	event2propagator[EV_PROPAGATE];
	event2propagator[EV_DECISIONLEVEL];
	event2propagator[EV_BACKTRACK];
	event2propagator[EV_MODELFOUND];
}

EventQueue::~EventQueue() {
	deleteList<Propagator>(allpropagators);
	for(auto lit2watch: lit2watches){
		deleteList<GenWatch>(lit2watch);
	}
}

bool EventQueue::isUnsat() const {
	return getPCSolver().satState() == SATVAL::UNSAT;
}

// NOTE: EACH propagator has to register here for the general methods
void EventQueue::accept(Propagator* propagator) {
	allpropagators.push_back(propagator);
}

void EventQueue::notifyNbOfVars(uint64_t nbvars) {
	while (lit2priority2propagators.size() < 2 * nbvars) {
		vector<proplist> newmap; // TODO number of priorities
		newmap.push_back( { });
		newmap.push_back( { });
		newmap.push_back( { });
		lit2priority2propagators.push_back(newmap);
		lit2watches.push_back( { });
	}
	var2decidable.resize(nbvars);
}

void EventQueue::acceptBounds(IntView* var, Propagator* propagator) {
	auto id = var->getVarID().id;
	if (intvarid2propagators.size() <= id) {
		MAssert(id<getMaxElem<unsigned int>());
		intvarid2propagators.resize(id + 1, proplist());
	}
	intvarid2propagators[id].push_back(propagator);
}

void EventQueue::notifyBoundsChanged(IntVar* var) {
	auto id = var->getVarID().id;
	for (auto i = intvarid2propagators[id].cbegin(); i < intvarid2propagators[id].cend(); ++i) {
		if(getPCSolver().terminateRequested()){
			_propagating = false;
			return;
		}
		if (!(*i)->isPresent()) {
			continue;
		}
		if (not (*i)->isQueued()) {
			(*i)->notifyQueued();
			fastqueue.push_back(*i);
		}
	}
}

void EventQueue::accept(Propagator* propagator, const Lit& litevent, PRIORITY priority) {
	if (not getPCSolver().isDecisionVar(var(litevent)) && dynamic_cast<LazyResidual*>(propagator)==NULL) {
		getPCSolver().notifyDecisionVar(var(litevent));
	}
	auto& list = lit2priority2propagators[toInt(litevent)][priority];
	list.push_back(propagator);
	if (getPCSolver().value(litevent) == l_True && not propagator->isQueued()) {
		propagator->notifyQueued();
		switch (priority) {
		case PRIORITY::FASTEST:
			fastestqueue.push_back(propagator);
			break;
		case PRIORITY::FAST:
			fastqueue.push_back(propagator);
			break;
		case PRIORITY::SLOW:
			slowqueue.push_back(propagator);
			break;
		}
	}
}

void EventQueue::accept(GenWatch* const watch) {
	if (not getPCSolver().isDecisionVar(var(watch->getPropLit()))) {
		getPCSolver().notifyDecisionVar(var(watch->getPropLit()));
	}
	bool addwatch = true;
	if (getPCSolver().value(watch->getPropLit()) == l_True) {
		// are propagated asap, but not in this method as that leads to correctness issues
		propagatewatchesasap.push_back(watch);
		if (watch->dynamic()) {
			addwatch = false;
		}
	}
	if (addwatch) {
		watch->addToNetwork();
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
	auto& lw = lit2watches[toInt(l)];
	if (lw.size() != 0) {
		for (uint i = 0; i != lw.size(); ++i) {
			lw[i]->propagate();
		}
		watchlist remwatches;
		for (auto i = lw.cbegin(); i != lw.cend(); ++i) {
			if (not (*i)->dynamic()) {
				remwatches.push_back(*i);
			} else {
				(*i)->removeFromNetwork(); // TODO delete dynamic watch? (might not be allowed here)
			}
		}
		lw = remwatches;
	}
	setTrue(lit2priority2propagators[toInt(l)][FASTEST], fastestqueue);
	setTrue(lit2priority2propagators[toInt(l)][FAST], fastqueue);
	setTrue(lit2priority2propagators[toInt(l)][SLOW], slowqueue);
}

rClause EventQueue::notifyFullAssignmentFound() {
	auto confl = nullPtrClause;
	for (auto i = event2propagator[EV_MODELFOUND].cbegin(); i < event2propagator[EV_MODELFOUND].cend(); ++i) {
		if ((*i)->isPresent()) {
			confl = (*i)->notifyFullAssignmentFound();
		}
		if(confl!=nullPtrClause || not getPCSolver().isTwoValued()){
			break;
		}
	}
	return confl;
}

bool EventQueue::queuesNotEmpty() const {
	return fastestqueue.size() > 0 || fastqueue.size() > 0 || slowqueue.size() > 0;
}

Propagator* EventQueue::getAndRemoveFirstPropagator() {
	MAssert(queuesNotEmpty());
	Propagator* p = NULL;
	if (fastestqueue.size() > 0) {
		p = fastestqueue.front();
		fastestqueue.pop_front();
	} else if (fastqueue.size() > 0) {
		p = fastqueue.front();
		fastqueue.pop_front();
	} else {
		p = slowqueue.front();
		slowqueue.pop_front();
	}
	return p;
}

rClause EventQueue::notifyPropagate() {
	MAssert(not _backtracking);

	auto confl = nullPtrClause;

	_requestedmore = true;
	if (_propagating) {
		return confl;
	}
	_propagating = true;

//	while (_requestedmore && confl==nullPtrClause) {
		_requestedmore = false;
		for (auto i = propagatewatchesasap.cbegin(); i < propagatewatchesasap.cend() && confl == nullPtrClause; ++i) {
			if(getPCSolver().terminateRequested()){
				_propagating = false;
				return confl;
			}
			(*i)->propagate();
		}
		propagatewatchesasap.clear();

		confl = runEternalPropagators();

		if (confl != nullPtrClause) {
			_propagating = false;
			return confl;
		}

		MAssert(getPCSolver().satState()!=SATVAL::UNSAT);
		while (queuesNotEmpty() && confl == nullPtrClause) {
			if(getPCSolver().terminateRequested()){
				_propagating = false;
				return confl;
			}
			auto p = getAndRemoveFirstPropagator();
			p->notifyDeQueued();
			if (p->isPresent()) {
				confl = p->notifypropagate();
				MAssert(getPCSolver().satState()!=SATVAL::UNSAT || confl!=nullPtrClause);
				if (confl == nullPtrClause) { // TODO AND something changed?
					confl = runEternalPropagators(); // Always immediately go to unit propagation after any other propagation
				}
			}
			MAssert(getPCSolver().satState()!=SATVAL::UNSAT || confl!=nullPtrClause);
		}
//	}

	_propagating = false;
	return confl;
}

rClause EventQueue::runEternalPropagators() {
	auto confl = nullPtrClause;
	auto& props = event2propagator.at(EV_PROPAGATE);
	for (uint i = 0; i < props.size() && confl == nullPtrClause; ++i) {
		if(getPCSolver().terminateRequested()){
			_propagating = false;
			return confl;
		}
		confl = props[i]->notifypropagate();
	}
	return confl;
}

void EventQueue::accept(ConstraintVisitor& visitor) {
	for (auto i = allpropagators.cbegin(); i < allpropagators.cend(); ++i) {
		(*i)->accept(visitor);
	}
}

uint EventQueue::size(EVENT event) const {
	return event2propagator.at(event).size();
}

void EventQueue::acceptForDecidable(Atom v, Propagator* prop) {
	MAssert((uint)v<var2decidable.size());
	if (not getPCSolver().isDecisionVar(v)) {
		var2decidable[v].push_back(prop);
	} else {
		prop->notifyQueued();
		fastqueue.push_back(prop);
	}
}

void EventQueue::notifyBecameDecidable(Atom v) {
	MAssert((uint)v<var2decidable.size());
	for (auto i = var2decidable[v].cbegin(); i < var2decidable[v].cend(); ++i) {
		(*i)->notifyQueued();
		fastqueue.push_back(*i);
	}
	var2decidable[v].clear();
}

void EventQueue::notifyNewDecisionLevel() {
	if (backtrackedtoroot) {
		backtrackedtoroot = false;
		if(not getPCSolver().modes().lazy && nbrestarts%10 == 0){
			clearNotPresentPropagators();
		}
	}
	auto& props = event2propagator.at(EV_DECISIONLEVEL);
	for (uint i = 0; i < size(EV_DECISIONLEVEL); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->notifyNewDecisionLevel();
	}
}

void EventQueue::notifyBacktrack(int untillevel, const Lit& decision) {
	MAssert(not _backtracking);
	_backtracking = true;
	_propagating = true;
	auto& props = event2propagator.at(EV_BACKTRACK);
	for (uint i = 0; i < size(EV_BACKTRACK); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->notifyBacktrack(untillevel, decision);
	}
	if(untillevel == 0){
		backtrackedtoroot = true;
		nbrestarts++;
	}
	_backtracking = false;
	_propagating = false;
}

int EventQueue::getNbOfFormulas() const {
	int size = 0;
	for (auto i = allpropagators.cbegin(); i < allpropagators.cend(); ++i) {
		size += (*i)->getNbOfFormulas();
	}
	return size;
}

void EventQueue::clearNotPresentPropagators() {
	//IMPORTANT: the propagators which are no longer present should be deleted from EVERY datastructure that is used later on!
	for (auto i = lit2priority2propagators.begin(); i < lit2priority2propagators.end(); ++i) {
		for (auto j = (*i).begin(); j != (*i).end(); ++j) {
			if (j->size() == 0) {
				continue;
			}
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
		if (i->size() == 0) {
			continue;
		}
		auto temp = *i;
		i->clear();
		for (auto prop = temp.cbegin(); prop != temp.cend(); ++prop) {
			if ((*prop)->isPresent()) {
				i->push_back(*prop);
			}
		}
	}

	for (auto i = event2propagator.begin(); i != event2propagator.end(); ++i) {
		if (i->second.size() == 0) {
			continue;
		}
		auto temp = i->second;
		i->second.clear();
		for (auto prop = temp.cbegin(); prop != temp.cend(); ++prop) {
			if ((*prop)->isPresent()) {
				i->second.push_back(*prop);
			}
		}
	}
}
