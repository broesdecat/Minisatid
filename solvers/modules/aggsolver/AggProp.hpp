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
#include <algorithm>
#include <tr1/memory>

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;

class PCSolver;
class AggSolver;

namespace Aggrs{

class TypedSet;
typedef std::map<int, Aggrs::TypedSet*> mips;
typedef std::vector<Aggrs::TypedSet*> vps;

class Watch;
class AggReason;

class Propagator;

class Agg{
private:
	TypedSet*	set;
	Weight		bound;
	AggSign 	sign;
	Lit			head;
	AggSem		sem;
	int			index;
	AggType		type;
	bool		optim;

public:
	Agg(const Weight& bound, AggSign sign, const Lit& head, AggSem sem, AggType type, bool optim = false):
		set(NULL), bound(bound), sign(sign), head(head), sem(sem), index(-1), type(type), optim(optim){	}

	TypedSet*	getSet		()					const	{ return set; }
	const Lit& 	getHead		() 					const 	{ return head; }
	int			getIndex	()					const	{ return index; }
	int			getSetID	()					const	;
	const Weight& getBound	() 					const	{ return bound; }
	bool 		isLower		()					const	{ return sign!=UB; }
	bool 		isUpper		()					const	{ return sign!=LB; }
	bool 		isDefined	()					const	{ return sem==DEF; }
	AggSem		getSem		()					const	{ return sem; }
	AggSign		getSign		()					const	{ return sign; }
	AggType		getType		()					const	{ return type; }
	bool		isOptim		()					const	{ return optim; }
	void 		setIndex	(int ind) 					{ index = ind; }
	void		setBound	(const Weight& w)			{ bound = w;}
	void		setSign		(const AggSign& s)			{ sign = s;}
	void		setType		(const AggType& s)			{ type = s;}
	void		setOptim	()							{ optim = true; }
	void		setTypedSet	(TypedSet * const s)		{ set = s; }
};
typedef std::vector<Agg*> vpagg;

class AggProp{
private:
	static std::tr1::shared_ptr<AggProp> max;
	static std::tr1::shared_ptr<AggProp> prod;
	static std::tr1::shared_ptr<AggProp> card;
	static std::tr1::shared_ptr<AggProp> sum;
public:
	static AggProp const * getMax() { return max.get(); }
	static AggProp const * getProd() { return prod.get(); }
	static AggProp const * getCard() { return card.get(); }
	static AggProp const * getSum() { return sum.get(); }

	virtual const char*	getName					() 										const = 0;
	virtual AggType 	getType					() 										const = 0;
	virtual bool 		isNeutralElement		(const Weight& w)						const = 0;
	virtual bool 		isMonotone				(const Agg& agg, const WL& l) 			const = 0;
	virtual Weight 		getBestPossible			(TypedSet* set) 						const = 0;
	virtual Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const = 0;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const = 0;

	virtual Weight		add						(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight		remove					(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) 	const = 0;

	virtual Propagator*	createPropagator		(TypedSet* set, bool pw) const = 0;
};

class MaxProp: public AggProp{
public:
	const char* getName					() 										const { return "MAX"; }
	AggType 	getType					() 										const { return MAX; }
	bool 		isNeutralElement		(const Weight& w) 						const { return false; }
	bool 		isMonotone				(const Agg& agg, const WL& l) 			const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const { assert(false); return 0; }
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const { assert(false); return 0; }
	bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) 	const;
	Propagator*	createPropagator		(TypedSet* set, bool pw) const;
};

class SPProp: public AggProp{
public:
	bool 		canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) 	const;
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
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
	Propagator*	createPropagator		(TypedSet* set, bool pw) const;
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
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
	Propagator*	createPropagator		(TypedSet* set, bool pw) const;
};

class CardProp: public SumProp{
public:
	const char* getName					() 										const { return "CARD"; }
	AggType		getType					() 										const { return CARD; }
	Weight		add						(const Weight& lhs, const Weight& rhs) 	const;
	Weight		remove					(const Weight& lhs, const Weight& rhs) 	const;
	Weight 		getBestPossible			(TypedSet* set) 						const;
	Weight 		getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two, TypedSet* set) const;
};

//Compare WLs by their literals, placing same literals next to each other
bool compareWLByLits(const WL& one, const WL& two);
//Compare WLs by their weights
bool compareWLByWeights(const WL& one, const WL& two);

/**
 * Checks whether the same literal occurs multiple times in the set
 * If this is the case, all identical literals are combined into one.
 *
 * @post: the literals are sorted according to weight again
 */
bool transformSetReduction(TypedSet* set, vps& sets);
bool transformTypePartition(TypedSet* set, vps& sets);
bool transformAddTypes(TypedSet* set, vps& sets);
bool transformMinToMax(TypedSet* set, vps& sets);
bool transformVerifyWeights(TypedSet* set, vps& sets);
bool transformOneToOneSetToAggMapping(TypedSet* set, vps& sets);
bool transformOneToOneSetToSignMapping(TypedSet* set, vps& sets);
bool transformCardGeqOneToEquiv(TypedSet* set, vps& sets);

bool transformSumsToCNF(vps& sets, MinisatID::PCSolver* pcsolver);

class Propagator {
protected:
	TypedSet* set; //Non-owning
public:
	Propagator(TypedSet* set):set(set){}
	virtual ~Propagator(){};

	virtual void 		initialize(bool& unsat, bool& sat);
	virtual rClause 	propagate		(const Lit& p, Watch* w, int level) = 0;
	virtual rClause 	propagate		(const Agg& agg, int level) = 0;
	virtual rClause		propagateAtEndOfQueue(int level) = 0;
	virtual void		backtrack		(int nblevels, int untillevel) = 0;
    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) = 0;

    TypedSet&			getSet() { return *set; }
    TypedSet*			getSetp() const { return set; }

    ///////
    // HELP METHODS
    ///////

    AggSolver* 			getSolver	() const;
    rClause 			notifySolver(AggReason* reason);
    lbool 				value		(const Lit& l) const;
};

class TypedSet{
protected:
	Weight 	esv;
	vwl 	wl;

	AggProp const * 	type;

	vpagg			 	aggregates;	//OWNS the pointers
	AggSolver*			aggsolver;	//does NOT own this pointer
	Propagator* 		prop;		//OWNS pointer

	int setid;

public:
	TypedSet(AggSolver* solver, int setid): esv(0), type(NULL), aggsolver(solver), prop(NULL), setid(setid){}
	virtual ~TypedSet(){
		deleteList<Agg>(aggregates);
		delete prop;
	}

	int				getSetID		() 			const 			{ return setid; }

	AggSolver *		getSolver		()			const			{ return aggsolver; }
	const vwl&		getWL			()			const 			{ return wl; }
	void			setWL			(const vwl& wl2)			{ wl=wl2; sort(wl.begin(), wl.end(), compareWLByWeights);} //FIXME SORT?

	const std::vector<Agg*>& getAgg		()	 						{ return aggregates; }
	std::vector<Agg*>& getAggNonConst	()	 						{ return aggregates; }
	void			replaceAgg		(const vpagg& repl)			;
	void 			addAgg			(Agg* aggr) 				;

	const Weight& 	getESV			() 			const 			{ return esv; }
	void 			setESV			(const Weight& w)			{ esv = w; }

	const AggProp&	getType			() 			const 			{ assert(type!=NULL); return *type; }
	void 			setType			(AggProp const * const w)	{ type = w; }

	void 			setProp			(Propagator* p) 			{ prop = p; }
	Propagator*		getProp			() 			const 			{ return prop; }


	void 			initialize		(bool& unsat, bool& sat);
	void			backtrack		(int nblevels, int untillevel) { getProp()->backtrack(nblevels, untillevel); }
	rClause 		propagate		(const Lit& p, Watch* w, int level) 	{ return getProp()->propagate(p, w, level); }
	rClause 		propagate		(const Agg& agg, int level) 			{ return getProp()->propagate(agg, level); }
	rClause			propagateAtEndOfQueue(int level) 						{ return getProp()->propagateAtEndOfQueue(level); }
	void 			getExplanation	(vec<Lit>& lits, const AggReason& ar) const { getProp()->getExplanation(lits, ar); }

	//	virtual bool canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;

	///////
	// HELP METHODS
	///////

	Weight				getBestPossible() { return getType().getBestPossible(this);}
};

}
}

#endif /* AGGPROP_HPP_ */
