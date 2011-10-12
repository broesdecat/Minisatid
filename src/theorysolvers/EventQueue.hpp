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
#include <deque>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/IntVar.hpp"

namespace MinisatID{

class PCSolver;
class IntVar;
class InnerModel;

typedef std::vector<Propagator*> proplist;
typedef std::vector<GenWatch*> watchlist;

// FIXME using iterators while the container can be changed is NOT allowed!

class EventQueue {
private:
	PCSolver& pcsolver;
	PCSolver& getPCSolver() { return pcsolver; }
	const PCSolver& getPCSolver() const { return pcsolver; }

	std::queue<Propagator*> fastqueue, slowqueue, backtrackqueue;

	proplist allpropagators;
	std::deque<Propagator*> finishparsing;
	std::map<EVENT, proplist > event2propagator;					// |events|
	std::vector<std::vector<proplist> > lit2priority2propagators;	// |lits|
	std::vector<watchlist> lit2watches;								// |lits|
	std::vector<proplist> intvarid2propagators; 					// |intvars|

	watchlist propagateasap;

	bool initialized;
	void notifyInitialized() { initialized = true; }
	bool isInitialized() const { return initialized; }

public:
	EventQueue(PCSolver& pcsolver);
	virtual ~EventQueue();


	// NOTE: EACH propagator has to register here for the general methods
	void accept(Propagator* propagator){
		for(proplist::const_iterator i=allpropagators.cbegin(); i<allpropagators.cend(); ++i){
			assert(propagator!=*i);
		}
		allpropagators.push_back(propagator);
	}

	void acceptForBacktrack(Propagator* propagator){
		backtrackqueue.push(propagator);
	}
	void acceptForPropagation(Propagator* propagator){
		fastqueue.push(propagator);
	}

	// NOTE: a propagator should only accept events when he is ready for those events!
	void accept(Propagator* propagator, EVENT basicevent){
		event2propagator[basicevent].push_back(propagator);
	}
	//NOTE Both aggsolver and modsolver can add rules during their initialization, so idsolver should be late and all the others early!
	void acceptFinishParsing(Propagator* propagator, bool late);
	void acceptBounds(IntView* var, Propagator* propagator){
		if(intvarid2propagators.size()<=(vsize)var->id()){
			intvarid2propagators.resize((vsize)var->id()+1, proplist());
		}
		intvarid2propagators[(vsize)var->id()].push_back(propagator);
	}
	void 	accept(Propagator* propagator, const Lit& litevent, PRIORITY priority);
	void 	accept(GenWatch* const watch);

	void 	addEternalPropagators();

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
	void 	notifyBoundsChanged		(IntVar* var);

	bool 	checkSymmetryAlgo1(const Lit& lit);
	bool	checkSymmetryAlgo2();

private:
	void 	setTrue(const proplist& list, std::queue<Propagator*>& queue);
	void 	clearNotPresentPropagators();

	uint size(EVENT event) const;
};
}

#endif /* EVENTQUEUE_HPP_ */
