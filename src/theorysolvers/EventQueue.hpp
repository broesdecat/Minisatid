/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef EVENTQUEUE_HPP_
#define EVENTQUEUE_HPP_

#include <vector>
#include <queue>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID{

class PCSolver;
class InnerModel;

class EventQueue {
private:
	PCSolver& pcsolver;
	PCSolver& getPCSolver() { return pcsolver; }
	const PCSolver& getPCSolver() const { return pcsolver; }


	std::queue<Propagator*> fastqueue, slowqueue;

	std::vector<Propagator*> allpropagators;

	std::map<EVENT, std::vector<Propagator*> > event2propagator;
	std::vector<std::vector<Propagator*> > varevent2propagator;

public:
	EventQueue(PCSolver& pcsolver);
	virtual ~EventQueue();

	void accept(Propagator* propagator){
		allpropagators.push_back(propagator);
	}

	void accept(Propagator* propagator, EVENT basicevent){ //register for events without extra information
		event2propagator[basicevent].push_back(propagator);
	}

	void acceptVarEvent(Propagator* propagator, Var varevent){
		varevent2propagator[varevent].push_back(propagator);
	}

	void notifyVarAdded();

	//FIXME a propagator should know whether propagate can already be called on it (because of not finished parsing yet)

	rClause notifyFullAssignmentFound();
	void 	finishParsing			(bool& unsat);
	void 	notifyNewDecisionLevel	();
	void 	notifyBacktrack			(int untillevel);
	rClause notifyPropagate			();
	Var 	notifyBranchChoice		(Var var);
	void 	printState				() const;
	void 	printStatistics			() const;
	void	setTrue					(const Lit& l);

};
}

#endif /* EVENTQUEUE_HPP_ */
