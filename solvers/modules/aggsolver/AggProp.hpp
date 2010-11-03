/*
 * AggProp.hpp
 *
 *  Created on: Oct 26, 2010
 *      Author: broes
 */

#ifndef AGGPROP_HPP_
#define AGGPROP_HPP_

#include "solvers/utils/Utils.hpp"
#include <vector>

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;
class AggSolver;

namespace Aggrs{

class TypedSet;

class Agg{
private:
	TypedSet*	set;
	Weight		bound;
	AggSign 	sign;
	Lit			head;
	AggSem		sem;
	int			index;
	int 		setid;
	AggType		type;
	bool		optim;

public:
	Agg(const Weight& bound, AggSign sign, const Lit& head, AggSem sem, AggType type, bool optim = false):
		bound(bound), sign(sign), head(head), sem(sem), index(-1), type(type), optim(optim){	}

	TypedSet*	getSet		()					const	{ return set; }
	const Lit& 	getHead		() 					const 	{ return head; }
	int			getIndex	()					const	{ return index; }
	int			getSetID	()					const	{ return setid; }
	const Weight& getBound	() 					const	{ return bound; }
	bool 		isLower		()					const	{ return sign!=UB; }
	bool 		isUpper		()					const	{ return sign!=LB; }
	bool 		isDefined	()					const	{ return sem==DEF; }
	AggSem		getSem		()					const	{ return sem; }
	AggSign		getSign		()					const	{ return sign; }
	AggType		getType		()					const	{ return type; }
	bool		isOptim		()					const	{ return optim; }
	void 		setIndex	(int ind) 					{ index = ind; }
	void 		setSetID	(int id)					{ setid = id; }
	void		setBound	(const Weight& w)			{ bound = w;}
	void		setOptim	()							{ optim = true; }
	void		setTypedSet	(TypedSet* s)				{ set = set; }
};

class AggProp{
private:
	static AggProp *max, *prod, *card, *sum;
public:
	static AggProp const * const getMax() { return max; }
	static AggProp const * const getProd() { return prod; }
	static AggProp const * const getCard() { return card; }
	static AggProp const * const getSum() { return sum; }

	virtual const char*	getName					() 										const = 0;
	virtual AggType 	getType					() 										const = 0;
	virtual bool 		isNeutralElement		(const Weight& w)						const = 0;
	virtual bool 		isMonotone				(const Agg& agg, const WL& l) 			const = 0;
	virtual Weight 		getBestPossible			(TypedSet* set) 						const = 0;
	virtual Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const = 0;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) = 0;
};

class MaxProp: public AggProp{
public:
	const char* getName					() 										const { return "MAX"; }
	AggType 	getType					() 										const { return MAX; }
	bool 		isNeutralElement		(const Weight& w) 						const { return false; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class SPProp: public AggProp{
public:
	virtual Weight	add					(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight	remove				(const Weight& lhs, const Weight& rhs) 	const = 0;
};

class ProdProp: public SPProp{
public:
	const char* getName					() 										const { return "PROD"; }
	AggType 	getType					() 										const { return PROD; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==1; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class SumProp: public SPProp{
public:
	const char* getName					() 										const { return "SUM"; }
	AggType 	getType					() 										const { return SUM; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==0; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class CardProp: public SumProp{
public:
	const char* getName					() 										const { return "CARD"; }
	AggType		getType					() 										const { return CARD; }
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set);
};

class AggSet{
private:
	vwl	wlits;
	std::vector<Agg*> aggs;

public:
    AggSet(const std::vector<WL>& wl);

    const 	vwl& 	getWL()	const						{ return wlits; }
			void 	setWL(const std::vector<WL>& newset);
};

class Propagator {
protected:
	TypedSet* set; //Non-owning
public:
	Propagator(TypedSet* set);
	virtual ~Propagator(){};

	// Propagate set literal
	virtual rClause 	propagate		(const Lit& p, Watch* w) = 0;
	// Propagate head
	virtual rClause 	propagate		(const Agg& agg) = 0;

    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) 	const = 0;

    virtual void 		initialize(bool& unsat, bool& sat);

    TypedSet&			getSet() { return *set; }
    AggSolver* 			getSolver();
    rClause 			notifySolver(AggReason* reason);
    lbool 				value(const Lit& l) const;
};

class TypedSet{
protected:
	Weight 	esv;
	vwl 	wl;

	AggProp* 	type; //does NOT own pointer TODO pointer is not destructed!

	std::vector<Agg*> 	aggregates;	//OWNS the pointers
	AggSolver*			aggsolver;	//does NOT own this pointer
	Propagator* 		prop;		//OWNS pointer

	int setid;

public:
	TypedSet(AggSolver* solver, int setid): aggsolver(solver), setid(setid){}
	virtual ~TypedSet(){
		deleteList<Agg>(aggregates);
		delete prop;
	}

	int				getSetID		() 			const 			{ return setid; }

	AggSolver * const getSolver		()			const			{ return aggsolver; }
	const vwl&		getWL			()			const 			{ return wl; }
	void			setWL(const vwl& wl2)			 			{ wl=wl2; } //TODO SORT?

	const std::vector<Agg*>& getAgg	()		 	const			{ return aggregates; }
	void 			addAgg			(Agg* aggr) { 	aggregates.push_back(aggr); }

	const Weight& 	getESV			() 			const 			{ return esv; }
	void 			setESV			(const Weight& w)			{ esv = w; }

	AggProp*	 	getType			() 			const 			{ return type; }
	void 			setType			(AggProp* w)				{ type = w; }

	void 			setProp			(Propagator* p) 			{ prop = p; }
	Propagator*		getProp			() 			const 			{ return prop; }


	void 			initialize		(bool& unsat, bool& sat)	{ getProp()->initialize(unsat, sat); }
	rClause 		propagate		(const Lit& p, Watch* w) 	{ return getProp()->propagate(p, w); }
	rClause 		propagate		(const Agg& agg) 			{ return getProp()->propagate(agg); }
	void 			getExplanation	(vec<Lit>& lits, const AggReason& ar) const { getProp()->getExplanation(lits, ar); }

	//	virtual bool canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;
};

//Compare WLs by their literals, placing same literals next to each other
bool compareWLByLits(const WL& one, const WL& two);

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
std::vector<TypedSet*> transformSetReduction(TypedSet* const set);
void transformSumsToCNF(bool& unsat, std::vector<TypedSet*> sets, MinisatID::PCSolver* pcsolver);

}
}

#endif /* AGGPROP_HPP_ */
