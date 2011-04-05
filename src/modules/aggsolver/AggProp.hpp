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

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"

#ifndef __GXX_EXPERIMENTAL_CXX0X__
#include <tr1/memory>
#endif

namespace Minisat{
	class Solver;
}

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;

class PCSolver;
class AggSolver;

class AggProp;
#ifdef __GXX_EXPERIMENTAL_CXX0X__
	typedef std::shared_ptr<AggProp> paggprop;
#else
	typedef std::tr1::shared_ptr<AggProp> paggprop;
#endif

class TypedSet;
typedef std::map<int, TypedSet*> mips;
typedef std::vector<TypedSet*> vps;

class Watch;
class AggReason;

class Propagator;

struct AggBound{
	Weight bound;
	AggSign sign;

	AggBound(AggSign sign, const Weight& b):bound(b), sign(sign){}
};

class Agg{
private:
	TypedSet*	set;
	AggBound	bound;
	Lit			head;
	AggSem		sem;
	int			defid;
	int			index;
	AggType		type;

public:
	Agg(const Lit& head, AggBound b, AggSem sem, int defid, AggType type):
		set(NULL), bound(b), head(head), sem(sem), defid(defid), index(-1), type(type){	}

	TypedSet*	getSet		()					const	{ return set; }
	const Lit& 	getHead		() 					const 	{ return head; }
	void	 	setHead		(const Lit& l)			 	{ head = l; }
	int			getIndex	()					const	{ return index; }

	const Weight&	getBound()					const	{ return bound.bound; }
	Weight	getCertainBound()					const;
	void		setBound	(AggBound b)				{ bound = b; }
	bool		hasUB		()					const	{ return bound.sign!=AGGSIGN_LB; }
	bool		hasLB		()					const	{ return bound.sign!=AGGSIGN_UB; }
	AggSign		getSign		()					const	{ return bound.sign; }

	bool 		isDefined	()					const	{ return sem==DEF; }
	AggSem		getSem		()					const	{ return sem; }
	int			getDefID	()					const	{ return defid; }
	AggType		getType		()					const	{ return type; }
	void 		setIndex	(int ind) 					{ index = ind; }
	void		setType		(const AggType& s)			{ type = s;}
	void		setTypedSet	(TypedSet * const s)		{ set = s; }
};
typedef std::vector<Agg*> agglist;

class AggProp{
private:
	static paggprop max;
	//static paggprop min;
	static paggprop prod;
	static paggprop card;
	static paggprop sum;
public:
	static AggProp const * getMax() { return max.get(); }
	//static AggProp const * getMin() { return min.get(); }
	static AggProp const * getProd() { return prod.get(); }
	static AggProp const * getCard() { return card.get(); }
	static AggProp const * getSum() { return sum.get(); }

	virtual const char*	getName					() 										const = 0;
	virtual AggType 	getType					() 										const = 0;
	virtual bool 		isNeutralElement		(const Weight& w)						const = 0;
	virtual bool 		isMonotone				(const Agg& agg, const Weight& w)		const = 0;

	//TODO expensive and in fact static: create variables and calc only once!
	//Calculate best and worst possible values for the EMPTY interpretation, independent of aggregate signs!
	virtual Weight		getMinPossible			(const TypedSet& set)					const = 0;
	virtual Weight		getMaxPossible			(const TypedSet& set)					const = 0;
	virtual Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const = 0;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const = 0;

	virtual Weight		add						(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight		remove					(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) 	const = 0;

	virtual Propagator*	createPropagator		(TypedSet* set) 						const = 0;
	virtual Weight 		getESV					()										const = 0;
};

class MaxProp: public AggProp{
public:
	const char* getName					() 										const { return "MAX"; }
	AggType 	getType					() 										const { return MAX; }
	bool 		isNeutralElement		(const Weight& w) 						const { return false; }
	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
	Weight		getMinPossible			(const TypedSet& set)					const;
	Weight		getMaxPossible			(const TypedSet& set)					const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const { return lhs>rhs?lhs:rhs; }
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const { assert(false); return 0; }
	bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) 	const;
	Propagator*	createPropagator		(TypedSet* set) 						const;

	Weight 		getESV					()										const { return negInfinity(); }
};

//class MinProp: public AggProp{
//public:
//	const char* getName					() 										const { return "MIN"; }
//	AggType 	getType					() 										const { return MIN; }
//	bool 		isNeutralElement		(const Weight& w) 						const { return false; }
//	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
//	Weight		getMinPossible			(const TypedSet& set)					const;
//	Weight		getMaxPossible			(const TypedSet& set)					const;
//	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
//	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
//	Weight		add						(const Weight& lhs, const Weight& rhs) 	const { return lhs<rhs?lhs:rhs; }
//	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const { assert(false); return 0; }
//	bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) 	const;
//	Propagator*	createPropagator		(TypedSet* set) 						const;
//
//	Weight 		getESV					()										const { return posInfinity(); }
//};

class SPProp: public AggProp{
public:
	bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust, bool real) 	const;
};

class ProdProp: public SPProp{
public:
	const char* getName					() 										const { return "PROD"; }
	AggType 	getType					() 										const { return PROD; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==1; }
	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight		getMinPossible			(const TypedSet& set)					const;
	Weight		getMaxPossible			(const TypedSet& set)					const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
	Propagator*	createPropagator		(TypedSet* set) const;

	Weight 		getESV					()										const { return Weight(1); }
};

class SumProp: public SPProp{
public:
	const char* getName					() 										const { return "SUM"; }
	AggType 	getType					() 										const { return SUM; }
	bool 		isNeutralElement		(const Weight& w) 						const { return w==0; }
	bool 		isMonotone				(const Agg& agg, const Weight& w)		const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight		getMinPossible			(const TypedSet& set)					const;
	Weight		getMaxPossible			(const TypedSet& set)					const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
	Propagator*	createPropagator		(TypedSet* set) const;

	Weight 		getESV					()										const { return Weight(0); }
};

class CardProp: public SumProp{
public:
	const char* getName					() 										const { return "CARD"; }
	AggType		getType					() 										const { return CARD; }
};

struct minmaxBounds{
	Weight min;
	Weight max;

	minmaxBounds(const Weight& min, const Weight& max):min(min),max(max){}
};

bool isSatisfied(const Agg& agg, const Weight& min, const Weight& max);
bool isSatisfied(const Agg& agg, const minmaxBounds& bounds);
bool isFalsified(const Agg& agg, const Weight& min, const Weight& max);
bool isFalsified(const Agg& agg, const minmaxBounds& bounds);
void addValue		(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds);
void addValue		(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max);
void removeValue	(const AggProp& type, const Weight& weight, bool addtoset, minmaxBounds& bounds);
void removeValue	(const AggProp& type, const Weight& weight, bool wasinset, Weight& min, Weight& max);

class Propagator {
private:
	TypedSet* const set; //Non-owning
	AggSolver* const aggsolver;
	Minisat::Solver* const satsolver;
public:
	Propagator(TypedSet* set);
	virtual ~Propagator(){};

	virtual void 		initialize(bool& unsat, bool& sat);
	virtual rClause 	propagate		(const Lit& p, Watch* w, int level) = 0;
	virtual rClause 	propagate		(int level, const Agg& agg, bool headtrue) = 0;
	virtual rClause		propagateAtEndOfQueue(int level) = 0;
	virtual void		backtrack		(int nblevels, int untillevel) = 0;
    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) = 0;

    TypedSet&			getSet() 			{ return *set; }
    const TypedSet&		getSet() 	const	{ return *set; }
    TypedSet*			getSetp()	const 	{ return set; }

    AggSolver*			getSolver() const { return aggsolver; }
	lbool				value(const Lit& l) const;

	//Assert: only call if model is two-valued!
	virtual Weight		getValue() const;
};

class TypedSet{
protected:
	Weight 				kb; //kb is "known bound", the value of the set reduced empty set
	vwl 				wl; // INVARIANT: sorted from lowest to highest weight! Except in set reduction operation!

	AggProp const * 	type;

	agglist			 	aggregates;	//OWNS the pointers
	AggSolver*			aggsolver;	//does NOT own this pointer
	Propagator* 		prop;		//OWNS pointer

	int 				setid;
	std::vector<AggTransformation*> transformations;

	bool				usingwatches;

public:
	TypedSet(AggSolver* solver, int setid):
			kb(Weight(0)),
			type(NULL),
			aggsolver(solver),
			prop(NULL),
			setid(setid),
			transformations(getTransformations()),
			usingwatches(true){}
	TypedSet(const TypedSet& set):
			kb(set.getKnownBound()),
			wl(set.getWL()),
			type(set.getTypep()),
			aggsolver(set.getSolver()),
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

	AggSolver *		getSolver		()			const			{ return aggsolver; }
	const vwl&		getWL			()			const 			{ return wl; }
	void			setWL			(const vwl& wl2)			{ wl=wl2; stable_sort(wl.begin(), wl.end(), compareWLByWeights);}

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

	void 			setProp			(Propagator* p) 			{ prop = p; }
	Propagator*		getProp			() 			const 			{ return prop; }

	const std::vector<AggTransformation*>& getTransformations() const { return transformations; }

	void 			initialize		(bool& unsat, bool& sat, vps& sets);
	void			backtrack		(int nblevels, int untillevel) 			{ getProp()->backtrack(nblevels, untillevel); }
	rClause 		propagate		(const Lit& p, Watch* w, int level) 	{ return getProp()->propagate(p, w, level); }
	rClause 		propagate		(const Agg& agg, int level, bool headtrue)	{ return getProp()->propagate(level, agg, headtrue); }
	rClause			propagateAtEndOfQueue(int level) 						{ return getProp()->propagateAtEndOfQueue(level); }
	void 			addExplanation	(AggReason& ar) const;
};

}

#endif /* AGGPROP_HPP_ */
