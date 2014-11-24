/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef FULLYWATCHED_HPP_
#define FULLYWATCHED_HPP_

#include "utils/Utils.hpp"

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

typedef std::vector<PropagationInfo> vprop;

class FWTrail{
public:
	int level;
	uint start; //Start is the propagation info from which the next propagatatend should start (first one not seen)
	Weight CBC, CBP;
	vprop props;
	std::vector<int> headindex; //The index of the aggregate of which the head was propagated
	std::vector<int> headtime; //The propindex of the propagated head

	FWTrail(int level, const Weight& CBC, const Weight& CBP): level(level), start(0), CBC(CBC), CBP(CBP){}
};

lbool 	canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP);

class FWAgg: public AggPropagator {
protected:
	/* Smart trail system:
	 * keep a datastructure with: currentBC, currentBP, decisionlevel and stack of propagations
	 */
	std::vector<FWTrail*> trail;

protected:
	virtual lbool 	initialize				(const Agg& agg);

	virtual void propagate(int level, Watch* ws, int aggindex);
	virtual void propagate(const Lit& p, Watch* ws, int level);

    virtual rClause propagateSpecificAtEnd	(const Agg& agg, bool headtrue) = 0;

    virtual void 	addToCertainSet			(const WL& l) = 0;
	virtual void 	removeFromPossibleSet	(const WL& l) = 0;

	void 			setCP					(const Weight& w) 			{ trail.back()->CBP = w; }
	void 			setCC					(const Weight& w) 			{ trail.back()->CBC = w; }

	std::vector<FWTrail*>&	getTrail		() 					 		{ return trail; }

public:
	FWAgg(TypedSet* set);
	virtual ~FWAgg();

	virtual void 	internalInitialize		(bool& unsat, bool& sat);
	virtual rClause reInitialize			() { return propagateAtEndOfQueue(); }
	virtual rClause	propagateAtEndOfQueue	();
	virtual void	backtrack				(int untillevel);
	virtual void 	getExplanation			(litlist& lits, const AggReason& ar) = 0;

	const Weight& 	getCP					()	const 	{ return trail.back()->CBP; }
	const Weight& 	getCC					()	const 	{ return trail.back()->CBC; }
};

class SPFWAgg: public  FWAgg {
public:
	SPFWAgg(TypedSet* agg);
	virtual ~SPFWAgg(){}

	void checkAddToExplan(bool& stop, Weight& min, Weight& max, const PropagationInfo& propinfo, const Agg& agg, bool caseone, std::vector<PropagationInfo>& reasons);
	virtual void 	getExplanation			(litlist& lits, const AggReason& ar);

protected:
	virtual rClause propagateSpecificAtEnd	(const Agg& agg, bool headtrue);
	virtual void 	addToCertainSet			(const WL& l);
	virtual void 	removeFromPossibleSet	(const WL& l);
};

class SumFWAgg: public  SPFWAgg {
public:
	SumFWAgg(TypedSet* agg);
	virtual ~SumFWAgg(){}

	virtual void 	internalInitialize				(bool& unsat, bool& sat);
};

class ProdFWAgg: public  SPFWAgg {
public:
	ProdFWAgg(TypedSet* agg);
	virtual ~ProdFWAgg(){}

	virtual void 	internalInitialize				(bool& unsat, bool& sat);
};

class MaxFWAgg: public  FWAgg {
public:
	MaxFWAgg(TypedSet* agg);
	virtual ~MaxFWAgg(){}

	virtual void 	internalInitialize				(bool& unsat, bool& sat);
	virtual void 	getExplanation			(litlist& lits, const AggReason& ar);

protected:
	virtual void 	addToCertainSet			(const WL& l);
	virtual void 	removeFromPossibleSet	(const WL& l);

	virtual rClause propagateSpecificAtEnd				(const Agg& agg, bool headtrue);
	virtual rClause propagateAll			(const Agg& agg, bool headtrue);
};

}

#endif /* FULLYWATCHED_HPP_ */
