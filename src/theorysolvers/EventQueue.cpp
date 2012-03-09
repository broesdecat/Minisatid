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
#include <typeinfo>

using namespace MinisatID;
using namespace std;

EventQueue::EventQueue(PCSolver& pcsolver)
		: pcsolver(pcsolver), initialized(false), finishing(false), allowpropagation(true) {
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
	event2propagator[EV_SYMMCHECK1];
	event2propagator[EV_SYMMCHECK2];
}

EventQueue::~EventQueue() {
	auto props = event2propagator.at(EV_EXITCLEANLY);
	for (uint i = 0; i < size(EV_EXITCLEANLY); ++i) {
		delete (props[i]);
	}
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
	for (vsize i = 0; i != lit2watches[toInt(l)].size(); ++i) {
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

void EventQueue::clearNotPresentPropagators() {
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

	if (getPCSolver().verbosity() > 0) {
		clog << ">>> Adding additional constraints to search\n";
	}

	while (finishparsing.size() > 0 && not isUnsat()) {
		while (finishparsing.size() > 0 && not isUnsat()) {
			auto prop = finishparsing.front();
			finishparsing.pop_front();
			bool present = true;
			prop->finishParsing(present);
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
		if (notifyPropagate() != nullPtrClause) {
			getPCSolver().notifyUnsat(); // TODO do something with the conflict clause?
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

int EventQueue::getNbOfFormulas() const {
	int count = 0;
	for (auto i = allpropagators.cbegin(); i < allpropagators.cend(); ++i) {
		if ((*i)->isPresent()) {
			count += (*i)->getNbOfFormulas();
		}
	}
	return count;
}

uint EventQueue::size(EVENT event) const {
	return event2propagator.at(event).size();
}

rClause EventQueue::notifyFullAssignmentFound() {
	rClause confl = nullPtrClause;
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
	return confl;
}

void EventQueue::acceptForDecidable(Var v, Propagator* prop) {
	MAssert(v<var2decidable.size());
	if (not getPCSolver().isDecisionVar(v)) {
		var2decidable[v].push_back(prop);
	} else {
		prop->notifypropagate();
	}
}

void EventQueue::notifyBecameDecidable(Var v) {
	MAssert(v<var2decidable.size());
	for (auto i = var2decidable[v].cbegin(); i < var2decidable[v].cend(); ++i) {
		propagatedecidables.push(*i);
	}
	var2decidable[v].clear();
}

void EventQueue::notifyClauseAdded(rClause clauseID) {
	auto props = event2propagator.at(EV_ADDCLAUSE);
	for (uint i = 0; i < size(EV_ADDCLAUSE); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->notifyClauseAdded(clauseID);
	}
}

bool EventQueue::symmetryPropagationOnAnalyze(const Lit& p) {
	auto props = event2propagator.at(EV_SYMMETRYANALYZE);
	for (uint i = 0; i < size(EV_SYMMETRYANALYZE); ++i) {
		if (props[i]->symmetryPropagationOnAnalyze(p)) {
			return true;
		}
	}
	return false;
}

// unsat if true
bool EventQueue::checkSymmetryAlgo1(const Lit& lit) {
	auto props = event2propagator.at(EV_SYMMCHECK1);
	for (uint i = 0; i < size(EV_SYMMCHECK1); ++i) {
		if (props[i]->checkSymmetryAlgo1(lit)) {
			return true;
		}
	}
	return false;
}

// return false if unsat
bool EventQueue::checkSymmetryAlgo2() {
	auto props = event2propagator.at(EV_SYMMCHECK2);
	for (uint i = 0; i < size(EV_SYMMCHECK2); ++i) {
		if (not props[i]->checkSymmetryAlgo2()) {
			return false;
		}
	}
	return true;
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

Var EventQueue::notifyBranchChoice(Var var) {
	auto props = event2propagator.at(EV_CHOICE);
	Var currentvar = var;
	for (uint i = 0; i < size(EV_CHOICE); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		currentvar = props[i]->notifyBranchChoice(currentvar);
	}
	return currentvar;
}

void EventQueue::printState() const {
	auto props = event2propagator.at(EV_PRINTSTATE);
	for (uint i = 0; i < size(EV_PRINTSTATE); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->printState();
	}
}

void EventQueue::printECNF(ostream&, set<Var>&) const {
	for (auto i = allpropagators.cbegin(); i < allpropagators.cend(); ++i) {
		//(*i)->printECNF(stream, printedvars); //TODO
	}
}

void EventQueue::printStatistics() const {
	auto props = event2propagator.at(EV_PRINTSTATS);
	for (uint i = 0; i < size(EV_PRINTSTATS); ++i) {
		if (!props[i]->isPresent()) {
			continue;
		}
		props[i]->printStatistics();
	}
}
