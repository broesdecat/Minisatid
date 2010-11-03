/*
 * FullyWatched.hpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#ifndef FULLYWATCHED_HPP_
#define FULLYWATCHED_HPP_

#include "solvers/utils/Utils.hpp"

#include "solvers/modules/aggsolver/AggComb.hpp"
#include "solvers/modules/aggsolver/AggProp.hpp"

namespace MinisatID {

namespace Aggrs{

///////
// DECLARATIONS
///////
class FWAgg: public Propagator {
protected:
	std::vector<PropagationInfo> 	stack;		// Stack of propagations of this expression so far.
	std::vector<lbool> truth, headvalue;
	std::vector<int> headindex;
	std::vector<bool> nomoreprops, optimagg;

	mutable std::vector<int> headproptime;

	Weight 	currentbestcertain, currentbestpossible;
					//current keeps the currently derived min and max bounds

protected:
	virtual lbool 	initialize(const Agg& agg);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const;

    virtual rClause propagate(const Agg& agg, bool headtrue) = 0;

    virtual void 	addToCertainSet(const WL& l) 			= 0;
	virtual void 	removeFromPossibleSet(const WL& l)		= 0;

	///////
	// GETTERS - SETTERS
	///////
	const Weight& 	getCP	() 					const 	{ return currentbestpossible; }
	void 			setCP	(const Weight& w) 			{ currentbestpossible = w; }
	const Weight& 	getCC	() 					const 	{ return currentbestcertain; }
	void 			setCC	(const Weight& w) 			{ currentbestcertain = w; }

	const std::vector<PropagationInfo>&	getStack() 					const 	{ return stack; }

public:
	FWAgg(TypedSet* set);
	virtual ~FWAgg(){};

	virtual void 	initialize(bool& unsat, bool& sat);

	virtual rClause propagate	(const Lit& p, Watch* ws);

// TODO dit is lelijk, maar het verplicht om eerst de root propagate op te roepen en daarna pas de lagere, maar er zullen wel betere manieren zijn.
	virtual rClause propagate(const Agg& agg);

	virtual void 	getExplanation(vec<Lit>& lits, const AggReason& ar) const;
};

class SPFWAgg: public  FWAgg {
public:
	SPFWAgg(TypedSet* agg);
	virtual ~SPFWAgg(){};

protected:
	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);

	virtual rClause propagate	(const Agg& agg, bool headtrue);
};

class SumFWAgg: public  SPFWAgg {
public:
	SumFWAgg(TypedSet* agg);
	virtual ~SumFWAgg(){};

	virtual void 	initialize	(bool& unsat, bool& sat);

			void	getMinimExplan		(const Agg& agg, vec<Lit>& lits);
			void 	addToBounds			(Agg& agg, const Weight& w);
};

class ProdFWAgg: public  SPFWAgg {
public:
	ProdFWAgg(TypedSet* agg);
	virtual ~ProdFWAgg(){};

	virtual void 	initialize	(bool& unsat, bool& sat);
};

class MaxFWAgg: public  FWAgg {
public:
	MaxFWAgg(TypedSet* agg);
	virtual ~MaxFWAgg(){};

	virtual void 	initialize	(bool& unsat, bool& sat);

protected:
	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);

	virtual rClause propagate	(const Agg& agg, bool headtrue);
	virtual rClause propagateAll(const Agg& agg, bool headtrue);
};

}

}

#endif /* FULLYWATCHED_HPP_ */
