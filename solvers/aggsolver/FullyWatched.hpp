/*
 * FullyWatched.hpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#ifndef FULLYWATCHED_HPP_
#define FULLYWATCHED_HPP_

#include "solvers/utils/Utils.hpp"

#include "solvers/aggsolver/AggComb.hpp"

namespace Aggrs{
	class Agg;
	class AggSet;

	typedef Agg* pagg;
	typedef vector<Agg*> vpagg;
	typedef AggSet* pset;

	class CalcAgg;
	typedef CalcAgg aggs;
	typedef aggs* paggs;

	class Propagator;
	typedef Propagator comb;
	typedef comb* pcomb;

	class Watch;
	typedef Watch* pw;

	class PropagationInfo;
	typedef vector<PropagationInfo> vprop;
}

///////
// DECLARATIONS
///////
namespace Aggrs{

class FWAgg: public Propagator {
protected:
	vprop 	stack;		// Stack of propagations of this expression so far.
	vector<lbool> truth, headvalue;
	vector<int> headindex;
	vector<bool> nomoreprops, optimagg;

	mutable vector<int> headproptime;

	Weight 	currentbestcertain, currentbestpossible;
					//current keeps the currently derived min and max bounds
public:
	FWAgg(paggs agg);
	virtual ~FWAgg(){};

	virtual void 	initialize(bool& unsat, bool& sat);
	virtual lbool 	initialize(const Agg& agg);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const;

	virtual rClause propagate	(const Lit& p, pw ws);

// TODO dit is lelijk, maar het verplicht om eerst de top propagate op te roepen en daarna pas de lagere, maar er zullen wel betere manieren zijn.
	virtual rClause propagate(const Agg& agg);
protected:
	virtual rClause propagate(const Agg& agg, bool headtrue) = 0;

public:
	virtual void 	getExplanation(vec<Lit>& lits, const AggReason& ar) const;
			bool	assertedBefore(const Var& l, const Var& p) const;	//TEMPORARY!!!
	virtual void 	backtrack	(const Watch& w);
	virtual void 	backtrack	(const Agg& agg);
	virtual void 	backtrack	(const Agg& agg, int stacksize);

	virtual void 	addToCertainSet(const WL& l) 			= 0;
	virtual void 	removeFromPossibleSet(const WL& l)		= 0;

	///////
	// GETTERS - SETTERS
	///////
	const Weight& 	getCP	() 					const 	{ return currentbestpossible; }
	void 			setCP	(const Weight& w) 			{ currentbestpossible = w; }
	const Weight& 	getCC	() 					const 	{ return currentbestcertain; }
	void 			setCC	(const Weight& w) 			{ currentbestcertain = w; }

	const vprop&	getStack() 					const 	{ return stack; }
};

class SPFWAgg: public  FWAgg, virtual public SPAggT{
public:
	SPFWAgg(paggs agg);
	virtual ~SPFWAgg(){};

	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);

	virtual rClause propagate	(const Agg& agg, bool headtrue);
};

class SumFWAgg: public  SPFWAgg, virtual public SumAggT{
public:
	SumFWAgg(paggs agg);
	virtual ~SumFWAgg(){};

	virtual void 	initialize	(bool& unsat, bool& sat);

			void	getMinimExplan		(const Agg& agg, vec<Lit>& lits);
			void 	addToBounds			(Agg& agg, const Weight& w);
};

class ProdFWAgg: public  SPFWAgg, virtual public ProdAggT {
public:
	ProdFWAgg(paggs agg);
	virtual ~ProdFWAgg(){};

	virtual void 	initialize	(bool& unsat, bool& sat);
};

class MaxFWAgg: public  FWAgg, virtual public MaxAggT {
public:
	MaxFWAgg(paggs agg);
	virtual ~MaxFWAgg(){};

	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);

	virtual rClause propagate	(const Agg& agg, bool headtrue);
	virtual rClause propagateAll(const Agg& agg, bool headtrue);

	virtual void 	initialize	(bool& unsat, bool& sat);
};

}

#endif /* FULLYWATCHED_HPP_ */
