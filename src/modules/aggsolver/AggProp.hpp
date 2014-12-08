/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGGPROP_HPP_
#define AGGPROP_HPP_

#include <vector>
#include <algorithm>
#include <memory>

#include "modules/aggsolver/AggUtils.hpp"

namespace MinisatID{

class AggProp;
typedef std::shared_ptr<AggProp> paggprop;

class TypedSet;
typedef std::map<int, TypedSet*> mips;
typedef std::vector<TypedSet*> vps;

class Watch;
class AggReason;

class AggPropagator;

class TempAgg{
private:
	AggBound	bound;
	Lit			head;
	AggSem		sem;
	int			index;
	AggType		type;

public:
	TempAgg(const Lit& head, AggBound b, AggSem sem, AggType type):
			bound(b), head(head), sem(sem), index(-1), type(type){
		MAssert(sem!=AggSem::DEF);
	}

	const Lit& 	getHead		() 					const 	{ return head; }
	void	 	setHead		(const Lit& l)			 	{ head = l; }
	int			getIndex	()					const	{ return index; }

	const Weight&	getBound()					const	{ return bound.bound; }
	void		setBound	(AggBound b)				{ bound = b; }
	bool		hasUB		()					const	{ return bound.sign!=AggSign::LB; }
	bool		hasLB		()					const	{ return bound.sign!=AggSign::UB; }
	AggSign		getSign		()					const	{ return bound.sign; }

	AggSem		getSem		()					const	{ return sem; }
	AggType		getType		()					const	{ return type; }
	void 		setIndex	(int ind) 					{ index = ind; }
	void		setType		(const AggType& s)			{ type = s;}
};
typedef std::vector<TempAgg*> tempagglist;

class Agg: public TempAgg{
private:
	bool optim;
	TypedSet*	set;

public:
	Agg(TypedSet* set, const TempAgg& agg, bool optim):
		TempAgg(agg), optim(optim), set(set){}

	TypedSet*	getSet			()	const	{ return set; }
	SATVAL		reInitializeAgg	();
	bool		isOptim			() const { return optim; }
};
typedef std::vector<Agg*> agglist;

class AggProp{
private:
	static paggprop max;
	static paggprop prod;
	static paggprop card;
	static paggprop sum;
public:
	virtual ~AggProp(){}

	static AggProp const * getMax() { return max.get(); }
	static AggProp const * getProd() { return prod.get(); }
	static AggProp const * getCard() { return card.get(); }
	static AggProp const * getSum() { return sum.get(); }

	virtual const char*	getName					() 										const = 0;
	virtual AggType 	getType					() 										const = 0;
	virtual bool 		isNeutralElement		(const Weight& w)						const = 0;
	virtual bool 		isMonotone				(const Agg& agg, const Weight& w)		const = 0;
	virtual bool 		isMonotone				(const TempAgg& agg, const Weight& w)	const = 0;

	Weight				getValue				(const TypedSet& set)					const;

	//TODO expensive and in fact static: create variables and calc only once!
	//Calculate best and worst possible values for the EMPTY interpretation, independent of aggregate signs!
	virtual Weight		getMinPossible			(const TypedSet& set)					const;
	virtual Weight		getMaxPossible			(const TypedSet& set)					const;
	virtual Weight		getMinPossible			(const std::vector<WL>& wls)			const = 0;
	virtual Weight		getMaxPossible			(const std::vector<WL>& wls)			const = 0;
	virtual Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const = 0;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, Weight& knownbound) const = 0;

	virtual Weight		add						(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight		removeMax				(const Weight& lhs, const Weight& rhs) 	const{
		return remove(lhs, rhs);
	}
	virtual Weight		removeMin				(const Weight& lhs, const Weight& rhs) 	const{
		return remove(lhs, rhs);
	}
	virtual AggPropagator*	createPropagator	(TypedSet* set) 						const = 0;
	virtual Weight 		getESV					()										const = 0;
protected:
	virtual Weight		remove					(const Weight& lhs, const Weight& rhs) 	const = 0;
};

class MaxProp: public AggProp{
public:
	const char* getName					() 										const { return "MAX"; }
	AggType 	getType					() 										const { return AggType::MAX; }
	bool 		isNeutralElement		(const Weight&) 						const { return false; }
	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
	bool 		isMonotone				(const TempAgg& agg, const Weight& w)	const;
	Weight		getMinPossible			(const std::vector<WL>& wls)			const;
	Weight		getMaxPossible			(const std::vector<WL>& wls)			const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, Weight& knownbound) const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const { return lhs>rhs?lhs:rhs; }
	Weight		remove					(const Weight&, const Weight&) 			const { MAssert(false); return 0; }
	AggPropagator*	createPropagator	(TypedSet* set) 						const;

	Weight 		getESV					()										const { return negInfinity(); }
};

class SPProp: public AggProp{
};

class ProdProp: public SPProp{
public:
	const char* getName					() 										const { return "PROD"; }
	AggType 	getType					() 										const { return AggType::PROD; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==1; }
	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
	bool 		isMonotone				(const TempAgg& agg, const Weight& w)	const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	virtual Weight	removeMax			(const Weight& lhs, const Weight& rhs) 	const;
	virtual Weight	removeMin			(const Weight& lhs, const Weight& rhs) 	const;
	Weight		getMinPossible			(const std::vector<WL>& wls)			const;
	Weight		getMaxPossible			(const std::vector<WL>& wls)			const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, Weight& knownbound) const;
	AggPropagator*	createPropagator	(TypedSet* set) const;

	Weight 		getESV					()										const { return Weight(1); }
protected:
	Weight remove(const Weight& lhs, const Weight& rhs) const;
};

class SumProp: public SPProp{
public:
	const char* getName					() 										const { return "SUM"; }
	AggType 	getType					() 										const { return AggType::SUM; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==0; }
	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
	bool 		isMonotone				(const TempAgg& agg, const Weight& w)	const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight		getMinPossible			(const std::vector<WL>& wls)			const;
	Weight		getMaxPossible			(const std::vector<WL>& wls)			const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, Weight& knownbound) const;
	AggPropagator*	createPropagator	(TypedSet* set) const;

	Weight 		getESV					()										const { return Weight(0); }
};

const AggProp * getType(AggType type);

class CardProp: public SumProp{
public:
	const char* getName					() 										const { return "CARD"; }
	AggType		getType					() 										const { return AggType::CARD; }
};

struct minmaxBounds{
	Weight min;
	Weight max;

	minmaxBounds(const Weight& min, const Weight& max):min(min),max(max){}
};

bool isSatisfied	(const TempAgg& agg, const Weight& min, const Weight& max);
bool isSatisfied	(const TempAgg& agg, const minmaxBounds& bounds);
bool isFalsified	(const TempAgg& agg, const Weight& min, const Weight& max);
bool isFalsified	(const TempAgg& agg, const minmaxBounds& bounds);
void addValue		(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds);
void addValue		(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max);
void removeValue	(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds);
void removeValue	(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max);

class PCSolver;

class AggPropagator {
private:
	TypedSet* const set; //Non-owning
public:
	AggPropagator(TypedSet* set);
	virtual ~AggPropagator(){}

	void 	initialize(bool& unsat, bool& sat);
	virtual rClause		reInitialize() = 0;
	virtual void 		propagate		(Watch* w);
	virtual rClause		propagateAtEndOfQueue() = 0;
	virtual void		backtrack		(int untillevel) = 0;
    virtual void 		getExplanation	(litlist& lits, const AggReason& ar) = 0;

    TypedSet&			getSet() 			{ return *set; }
    const TypedSet&		getSet() 	const	{ return *set; }
    TypedSet*			getSetp()	const 	{ return set; }

    const PCSolver&		getPCSolver() const;

	lbool				value(const Lit& l) const;

protected:
	virtual void internalInitialize(bool& unsat, bool& sat) = 0;

	virtual void propagate(int level, Watch* ws, int aggindex) = 0;
	virtual void propagate(const Lit& p, Watch* ws, int level) = 0;
};

}

#endif /* AGGPROP_HPP_ */
