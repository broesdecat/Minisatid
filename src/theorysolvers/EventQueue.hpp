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
class ConstraintVisitor;

typedef std::vector<Propagator*> proplist;
typedef std::deque<Propagator*> propqueue;
typedef std::vector<GenWatch*> watchlist;

// FIXME using iterators while the container can be changed is NOT allowed!

class EventQueue {
private:
	PCSolver& pcsolver;
	PCSolver& getPCSolver() { return pcsolver; }
	const PCSolver& getPCSolver() const { return pcsolver; }

	std::deque<Propagator*> fastqueue, slowqueue, backtrackqueue;

	proplist allpropagators;
	std::map<EVENT, propqueue > event2propagator;					// |events|
	std::vector<std::vector<proplist> > lit2priority2propagators;	// |lits|
	std::vector<watchlist> lit2watches;								// |lits|
	std::vector<proplist> intvarid2propagators; 					// |intvars|

	std::vector<std::vector<Propagator*>> var2decidable;			// |vars|

	watchlist propagatewatchesasap;

	bool initialized;
	void notifyInitialized() { initialized = true; }
	bool isInitialized() const { return initialized; }
	bool finishing;

	bool allowpropagation;

public:
	EventQueue(PCSolver& pcsolver);
	virtual ~EventQueue();

	// NOTE: EACH propagator has to register here for the general methods
	void accept(Propagator* propagator){
		for(proplist::const_iterator i=allpropagators.cbegin(); i<allpropagators.cend(); ++i){
			MAssert(propagator!=*i);
		}
		allpropagators.push_back(propagator);
	}

	void acceptForBacktrack(Propagator* propagator){
		backtrackqueue.push_back(propagator);
	}
	void acceptForPropagation(Propagator* propagator){
		fastqueue.push_back(propagator);
	}

	rClause notifyFullAssignmentFound();

	// NOTE: a propagator should only accept events when he is ready for those events!
	void accept(Propagator* propagator, EVENT basicevent){
		event2propagator[basicevent].push_back(propagator);
	}
	//NOTE Both aggsolver and modsolver can add rules during their initialization, so idsolver should be late and all the others early!
	void acceptFinishParsing(Propagator* propagator, bool late);
	void acceptBounds(IntView* var, Propagator* propagator){
		if(intvarid2propagators.size()<=(uint)var->id()){
			intvarid2propagators.resize((uint)var->id()+1, proplist());
		}
		intvarid2propagators[(uint)var->id()].push_back(propagator);
	}
	void 	accept(Propagator* propagator, const Lit& litevent, PRIORITY priority);
	void 	accept(GenWatch* const watch);

	void 	addEternalPropagators();

	void 	notifyVarAdded			();

	int		getNbOfFormulas			() const;

	void 	acceptForDecidable(Var v, Propagator* prop);
	void 	notifyBecameDecidable(Var v);
	void 	notifyNewDecisionLevel	();
	void 	notifyBacktrack			(int untillevel, const Lit& decision);
	rClause notifyPropagate			();
	void	setTrue					(const Lit& l);
	void 	notifyBoundsChanged		(IntVar* var);

	void 	accept(ConstraintVisitor& visitor);

	void 	initialize();

private:
	void 	setTrue(const proplist& list, std::deque<Propagator*>& queue);
	void 	clearNotPresentPropagators();

	bool 	isUnsat() const;

	uint size(EVENT event) const;
};
}

#endif /* EVENTQUEUE_HPP_ */
