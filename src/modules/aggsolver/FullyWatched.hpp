/*
 * FullyWatched.hpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#ifndef FULLYWATCHED_HPP_
#define FULLYWATCHED_HPP_

#include "utils/Utils.hpp"

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

namespace Aggrs{

typedef std::vector<PropagationInfo> vprop;

///////
// DECLARATIONS
///////

class FWTrail{
public:
	int level, start; //Start is the propagation info from which the next propagatatend should start (first one not seen)
	Weight CBC, CBP;
	vprop props;
	std::vector<int> headindex; //The index of the aggregate of which the head was propagated
	std::vector<int> headtime; //The propindex of the propagated head

	FWTrail(int level, const Weight& CBC, const Weight& CBP): level(level), start(0), CBC(CBC), CBP(CBP){}
};

lbool 	canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP, Expl& basedon);

class FWAgg: public Propagator {
protected:
	/*
	 * Smart trail system:
	 * keep a datastructure with: currentBC, currentBP, decisionlevel and stack of propagations
	 */
	std::vector<FWTrail*> trail;

	//std::vector<int> headindex;
	//std::vector<bool> nomoreprops;
	//mutable std::vector<int> headproptime;

protected:
	virtual lbool 	initialize				(const Agg& agg);

    virtual rClause propagateSpecificAtEnd	(const Agg& agg, bool headtrue) = 0;

    virtual void 	addToCertainSet			(const WL& l) = 0;
	virtual void 	removeFromPossibleSet	(const WL& l) = 0;

	///////
	// GETTERS - SETTERS
	///////
	void 			setCP					(const Weight& w) 			{ trail.back()->CBP = w; }
	void 			setCC					(const Weight& w) 			{ trail.back()->CBC = w; }

	std::vector<FWTrail*>&	getTrail		() 					 		{ return trail; }

public:
	FWAgg(TypedSet* set);
	virtual ~FWAgg(){};

	virtual void 	initialize				(bool& unsat, bool& sat);
	rClause 		propagate				(const Lit& p, Watch* ws, int level);
	rClause 		propagate				(int level, const Agg& agg, bool headtrue);
	rClause			propagateAtEndOfQueue	(int level);
	void		 	backtrack				(int nblevels, int untillevel);
	virtual void 	getExplanation			(vec<Lit>& lits, const AggReason& ar) = 0;

	const Weight& 	getCP					()	const 	{ return trail.back()->CBP; }
	const Weight& 	getCC					()	const 	{ return trail.back()->CBC; }
};

class SPFWAgg: public  FWAgg {
public:
	SPFWAgg(TypedSet* agg);
	virtual ~SPFWAgg(){};

	virtual void 	getExplanation			(vec<Lit>& lits, const AggReason& ar);

protected:
	virtual rClause propagateSpecificAtEnd	(const Agg& agg, bool headtrue);
	virtual void 	addToCertainSet			(const WL& l);
	virtual void 	removeFromPossibleSet	(const WL& l);
};

class SumFWAgg: public  SPFWAgg {
public:
	SumFWAgg(TypedSet* agg);
	virtual ~SumFWAgg(){};

	virtual void 	initialize				(bool& unsat, bool& sat);
};

class ProdFWAgg: public  SPFWAgg {
public:
	ProdFWAgg(TypedSet* agg);
	virtual ~ProdFWAgg(){};

	virtual void 	initialize				(bool& unsat, bool& sat);
};

class MaxFWAgg: public  FWAgg {
public:
	MaxFWAgg(TypedSet* agg);
	virtual ~MaxFWAgg(){};

	virtual void 	initialize				(bool& unsat, bool& sat);
	virtual void 	getExplanation			(vec<Lit>& lits, const AggReason& ar);

protected:
	virtual void 	addToCertainSet			(const WL& l);
	virtual void 	removeFromPossibleSet	(const WL& l);

	virtual rClause propagateSpecificAtEnd				(const Agg& agg, bool headtrue);
	virtual rClause propagateAll			(const Agg& agg, bool headtrue);
};

}

}

#endif /* FULLYWATCHED_HPP_ */
