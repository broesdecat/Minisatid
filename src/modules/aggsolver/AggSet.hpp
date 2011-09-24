/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGGSET_HPP_
#define AGGSET_HPP_

#include <vector>
#include <algorithm>

#include "modules/DPLLTmodule.hpp"

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

class TypedSet: public Propagator{
protected:
	Weight 				kb; //kb is "known bound", the value of the set reduced empty set
	vwl 				wl; // INVARIANT: sorted from lowest to highest weight! Except in set reduction operation!

	AggProp const * 	type;

	agglist			 	aggregates;	//OWNS the pointers
	AggPropagator* 		prop;		//OWNS pointer

	int 				setid;

	bool				usingwatches;

	std::map<Var, AggReason*>	reasons;

public:
	TypedSet(PCSolver* solver, int setid, const Weight& knownbound);
	TypedSet(const TypedSet& set);
	virtual ~TypedSet(){
		deleteList<Agg>(aggregates);
		delete prop;
	}

	int				getSetID		() 			const 			{ return setid; }

	const vwl&		getWL			()			const 			{ return wl; }
	void			setWL			(const vwl& wl2)			{ wl=wl2; stable_sort(wl.begin(), wl.end(), compareByWeights<WL>);}

	const std::vector<Agg*>& getAgg		()	const					{ return aggregates; }
	std::vector<Agg*>& getAggNonConst	()	 						{ return aggregates; }
	//void			replaceAgg		(const agglist& repl);
	//void			replaceAgg		(const agglist& repl, const agglist& del);
	void 			addAgg			(const TempAgg& aggr, bool optim);
	void 			removeAggs		(const std::set<Agg*>& del);

	bool			isUsingWatches() const { return usingwatches; }
	void			setUsingWatches(bool use) { usingwatches = use; }

	const Weight&	getKnownBound	()			const			{ return kb; }

	const AggProp&	getType			() 			const 			{ assert(type!=NULL); return *type; }
	AggProp const *	getTypep		() 			const 			{ return type; }
	void 			setType			(AggProp const * const w)	{
		type = w;
	}

	void 			setProp			(AggPropagator* p) 			{ prop = p; }
	AggPropagator*	getProp			() 			const 			{ return prop; }

	void 			addExplanation	(AggReason& ar) const;

	rClause 		notifySolver(AggReason* ar);

	// Propagator methods
	virtual const char* getName			() const { return "aggregate"; }
	virtual int		getNbOfFormulas		() const;
	virtual rClause getExplanation		(const Lit&);

	virtual rClause notifyFullAssignmentFound();
	virtual void 	finishParsing		(bool& present, bool& unsat);
		// Checks presence of aggregates and initializes all counters. UNSAT is set to true if unsat is detected
		// PRESENT is set to true if aggregate propagations should be done
	virtual void 	notifyNewDecisionLevel	();
	// NOTE: call explicitly when using hasnextprop/nextprop!
	virtual void 	notifyBacktrack		(int untillevel, const Lit& decision);
			void 	notifypropagate		(Watch* w);
	virtual rClause	notifypropagate		();
};

} /* namespace MinisatID */
#endif /* AGGSET_HPP_ */
