/*
 * AggProp.hpp
 *
 *  Created on: Oct 26, 2010
 *      Author: broes
 */

#ifndef AGGPROP_HPP_
#define AGGPROP_HPP_

#include "solvers/utils/Utils.hpp"

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;


class TypedSet{
private:
	Weight esv;
	vwl wl;

	//set -> aggs
	//propagator
	//esv
	//

public:

	Weight getESV() const { return esv; }
	void 	setESV(const Weight& w) { esv = w; }
	const vwl& getWL() const { return wl; }
};

class Agg{
private:
	Weight		bound;
	AggSign 		sign;
	Lit			head;
	AggSem		sem;

	int			index;

	bool		optim;

public:
	Agg(const Weight& bound, AggSign sign, const Lit& head, AggSem sem, bool optim = false):
		bound(bound), sign(sign), head(head), sem(sem), index(-1), optim(optim){	}

	const 	Lit& 		getHead() 			const 	{ return head; }
			int			getIndex()			const	{ return index; }
			void 		setIndex(int ind) 			{ index = ind; }

	const 	Weight& getBound() 		const	{ return bound; }
	const 	Weight& getLowerBound()	const	{ return bound; }
	const 	Weight& getUpperBound()	const	{ return bound;}
			void	setLowerBound(const Weight& w)	{ bound = w;}
			void	setUpperBound(const Weight& w)	{ bound = w;}
			bool 	isLower()		const			{ return sign!=UB; }
			bool 	isUpper()		const			{ return sign!=LB; }

			bool 	isDefined()		const	{ return sem==DEF; }

			AggSign	getSign()		const	{ return sign; }

			bool	isOptim()		const	{ return optim; }
};

class AggProp{
public:
	virtual const char*	getName() const = 0;
	virtual AggType 	getType() const = 0;
	virtual bool 		isNeutralElement	(const Weight& w) const = 0;
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) 	const = 0;
	virtual Weight 		getBestPossible			(TypedSet* set) const = 0;
	virtual Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const = 0;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) = 0;
};

class MaxProp: public AggProp{
public:
	const char* getName() const { return "MAX"; }
	AggType 	getType() const { return MAX; }
	bool 		isNeutralElement	(const Weight& w) const { return false; }
	bool 		isMonotone			(const Agg& agg, const WL& l) 	const;
	Weight 	getBestPossible			(TypedSet* set) 										const;
	Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) 			;
};

class SPProp: public AggProp{
public:
	virtual Weight		add		(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight		remove	(const Weight& lhs, const Weight& rhs) 	const = 0;
};

class ProdProp: public SPProp{
public:
	const char* getName() const { return "PROD"; }
	AggType 	getType() const { return PROD; }
	bool 		isNeutralElement(const Weight& w) const { return w==1; }
	bool 		isMonotone			(const Agg& agg, const WL& l) 	const;
	Weight		add		(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove	(const Weight& lhs, const Weight& rhs) 	const;
	Weight 	getBestPossible			(TypedSet* set) 										const;
	Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) 			;
};

class SumProp: public SPProp{
public:
	const char* getName				() const { return "SUM"; }
	AggType 	getType				() const { return SUM; }
	bool 		isNeutralElement	(const Weight& w) const { return w==0; }
	bool 		isMonotone			(const Agg& agg, const WL& l) 	const;
	Weight		add					(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove				(const Weight& lhs, const Weight& rhs) 	const;
	Weight 	getBestPossible			(TypedSet* set) 										const;
	Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) 			;
};

class CardProp: public SumProp{
public:
	AggType	getType					() const { return CARD; }
	const char* getName				() const { return "CARD"; }
	Weight	add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight	remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 	getBestPossible			(TypedSet* set) 										const;
	Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) 			;
};

}

#endif /* AGGPROP_HPP_ */
