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
	std::vector<AggTransformation*> transformations;

	bool				usingwatches;

public:
	TypedSet(PCSolver* solver, int setid):
			Propagator(solver),
			kb(Weight(0)),
			type(NULL),
			prop(NULL),
			setid(setid),
			transformations(MinisatID::getTransformations()),
			usingwatches(true){}
	TypedSet(const TypedSet& set):
			Propagator(set.pcsolver),
			kb(set.getKnownBound()),
			wl(set.getWL()),
			type(set.getTypep()),
			prop(NULL),
			setid(set.getSetID()),
			transformations(set.getTransformations()),
			usingwatches(set.isUsingWatches()){
	}
	virtual ~TypedSet(){
		deleteList<Agg>(aggregates);
		delete prop;
	}

	int				getSetID		() 			const 			{ return setid; }

	const vwl&		getWL			()			const 			{ return wl; }
	void			setWL			(const vwl& wl2)			{ wl=wl2; stable_sort(wl.begin(), wl.end(), compareByWeights<WL>);}

	const std::vector<Agg*>& getAgg		()	const					{ return aggregates; }
	std::vector<Agg*>& getAggNonConst	()	 						{ return aggregates; }
	void			replaceAgg		(const agglist& repl);
	void			replaceAgg		(const agglist& repl, const agglist& del);
	void 			addAgg			(Agg* aggr);

	bool			isUsingWatches() const { return usingwatches; }
	void			setUsingWatches(bool use) { usingwatches = use; }

	const Weight&	getKnownBound	()			const			{ return kb; }
	void 			setKnownBound	(const Weight& w)			{ kb = w; }

	const AggProp&	getType			() 			const 			{ assert(type!=NULL); return *type; }
	AggProp const *	getTypep		() 			const 			{ return type; }
	void 			setType			(AggProp const * const w)	{
		type = w;
	}

	void 			setProp			(AggPropagator* p) 			{ prop = p; }
	AggPropagator*	getProp			() 			const 			{ return prop; }

	const std::vector<AggTransformation*>& getTransformations() const { return transformations; }

	void 			initialize		(bool& unsat, bool& sat);
	void			backtrack		(int untillevel) 			{ getProp()->backtrack(untillevel); }
	rClause 		propagate		(const Lit& p, Watch* w, int level) 	{ return getProp()->propagate(p, w, level); }
	rClause 		propagate		(const Agg& agg, int level, bool headtrue)	{ return getProp()->propagate(level, agg, headtrue); }
	rClause			propagateAtEndOfQueue(int level) 						{ return getProp()->propagateAtEndOfQueue(level); }
	void 			addExplanation	(AggReason& ar) const;

	rClause 		notifySolver(AggReason* ar);

	// FIXME
	// Propagator methods
	virtual const char* getName			() const { return "aggregate"; }
	virtual rClause getExplanation		(const Lit&);
	virtual rClause notifyFullAssignmentFound();
	virtual void 	finishParsing		(bool& present, bool& unsat);
		// Checks presence of aggregates and initializes all counters. UNSAT is set to true if unsat is detected
		// PRESENT is set to true if aggregate propagations should be done
	virtual void 	notifyNewDecisionLevel	();
	// NOTE: call explicitly when using hasnextprop/nextprop!
	virtual void 	notifyBacktrack		(int untillevel, const Lit& decision);
	virtual rClause	notifypropagate		()							{ assert(false); return nullPtrClause; }
	virtual Var 	notifyBranchChoice	(const Var& var) const 		{ assert(false); return var; }
	virtual void 	printStatistics		() const 					{ assert(false); }
	virtual void 	printState			() const 					{ assert(false); }
	virtual int		getNbOfFormulas		() const 					{ return 0; }
	virtual void 	notifyClauseAdded	(rClause) 					{ assert(false); }
	virtual void 	notifyClauseDeleted	(rClause) 					{ assert(false); }
	virtual bool 	symmetryPropagationOnAnalyze(const Lit&) 		{ assert(false); return false; }
};

} /* namespace MinisatID */
#endif /* AGGSET_HPP_ */
