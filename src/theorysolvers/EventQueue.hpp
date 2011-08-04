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

typedef std::vector<Propagator*> proplist;

class EventQueue {
private:
	PCSolver& pcsolver;
	PCSolver& getPCSolver() { return pcsolver; }
	const PCSolver& getPCSolver() const { return pcsolver; }

	std::queue<Propagator*> fastqueue, slowqueue;

	proplist allpropagators;

	std::map<EVENT, proplist > event2propagator;
	proplist earlyfinishparsing, latefinishparsing;
	std::vector<std::vector<proplist> > litevent2propagator;

	bool initialized;
	void notifyInitialized() { initialized = true; }
	bool isInitialized() const { return initialized; }

public:
	EventQueue(PCSolver& pcsolver);
	virtual ~EventQueue();


	// NOTE: EACH propagator has to register here for the general methods
	void accept(Propagator* propagator){
		for(proplist::const_iterator i=allpropagators.begin(); i<allpropagators.end(); ++i){
			assert(propagator!=*i);
		}
		allpropagators.push_back(propagator);
	}

	// NOTE: a propagator should only accept events when he is ready for those events!
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

	void 	addEternalPropagators();
	void 	acceptLitEvent(Propagator* propagator, const Lit& litevent, PRIORITY priority);

	void 	notifyVarAdded			();

	int		getNbOfFormulas			() const;

	void 	notifyClauseAdded(rClause clauseID);
	void 	notifyClauseDeleted(rClause clauseID);
	bool 	symmetryPropagationOnAnalyze(const Lit& p);
	rClause notifyFullAssignmentFound();
	void 	finishParsing			(bool& unsat);
	void 	notifyNewDecisionLevel	();
	void 	notifyBacktrack			(int untillevel, const Lit& decision);
	rClause notifyPropagate			();
	Var 	notifyBranchChoice		(Var var);
	void 	printState				() const;
	void 	printStatistics			() const;
	void	setTrue					(const Lit& l);

private:
	void 	setTrue(const proplist& list, std::queue<Propagator*>& queue);

	proplist::const_iterator begin(EVENT event) const;
	proplist::const_iterator end(EVENT event) const;
};
}

#endif /* EVENTQUEUE_HPP_ */
