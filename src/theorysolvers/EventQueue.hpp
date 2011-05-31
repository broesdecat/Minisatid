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
	std::vector<Propagator*> earlyfinishparsing, latefinishparsing;
	std::vector<std::map<PRIORITY, std::vector<Propagator*> > > litevent2propagator;

public:
	EventQueue(PCSolver& pcsolver);
	virtual ~EventQueue();


	// IMPORTANT: EACH propagator has to register her (takes care of deletion)
	void accept(Propagator* propagator){
		allpropagators.push_back(propagator);
	}

	// IMPORTANT: a propagator should only accept events when he is ready for those events!
	void accept(Propagator* propagator, EVENT basicevent){
		event2propagator[basicevent].push_back(propagator);
	}
	//NOTE Both aggsolver and modsolver can add rules during their initialization, so idsolver should be late and all the others early!
	void acceptFinishParsing(Propagator* propagator, bool late){
		if(late){
			latefinishparsing.push_back(propagator);
		}else{
			earlyfinishparsing.push_back(propagator);
		}
	}

	//TODO should check doubles in another way (or prevent any from being added) (maybe a set is better than a vector)
	void acceptLitEvent(Propagator* propagator, const Lit& litevent, PRIORITY priority){
		for(std::vector<Propagator*>::const_iterator i=litevent2propagator[toInt(litevent)].at(priority).begin(); i<litevent2propagator[toInt(litevent)].at(priority).end(); ++i){
			if((*i)==propagator){
				return;
			}
		}
		litevent2propagator[toInt(litevent)].at(priority).push_back(propagator);
	}

	void 	notifyVarAdded();

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
