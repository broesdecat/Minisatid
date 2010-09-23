/*
 * AggComb.hpp
 *
 *  Created on: Aug 26, 2010
 *      Author: broes
 */

#ifndef AGGCOMB_HPP_
#define AGGCOMB_HPP_

#include "solvers/utils/Utils.hpp"

#include <vector>

///////
// FORWARD DECLARATIONS + TYPEDEFS
///////
class AggSolver;
typedef AggSolver* paggsol;

class WL;
typedef vector<Weight> vw;
typedef vector<Lit> vl;
typedef vector<WL> vwl;

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


class AggSet{
private:
	vwl	wlits;

public:
    AggSet(const vector<WL>& wl);

    const 	vwl& 	getWL()	const						{ return wlits; }
			void 	setWL(const vector<WL>& newset);
};

class Agg{
private:
	Weight		bound;
	Bound 		sign;
	Lit			head;
	HdEq		sem;

	CalcAgg* 	comb;
	int			index;

	bool		optim;

public:
	Agg(const Weight& bound, Bound sign, const Lit& head, HdEq sem, bool optim = false):
		bound(bound), sign(sign), head(head), sem(sem), comb(NULL), index(-1), optim(optim){	}

	const 	Lit& 		getHead() 			const 	{ return head; }
			void 		setComb(CalcAgg* c, int ind) { comb = c; index = ind;	}
			CalcAgg* 	getAggComb() 		const 	{ return comb; }
			int			getIndex()			const	{ return index; }
			void 		setIndex(int ind) 			{ index = ind; }

	const 	Weight& getBound() 		const	{ return bound; }
	const 	Weight& getLowerBound()	const	{ return bound; }
	const 	Weight& getUpperBound()	const	{ return bound;}
			void	setLowerBound(const Weight& w)	{ bound = w;}
			void	setUpperBound(const Weight& w)	{ bound = w;}
			bool 	isLower()		const			{ return sign!=UPPERBOUND; }
			bool 	isUpper()		const			{ return sign!=LOWERBOUND; }

			bool 	isDefined()		const	{ return sem==DEF; }

			Bound	getSign()		const	{ return sign; }

			bool	isOptim()		const	{ return optim; }
};


enum Occurrence {HEAD, POS, NEG};

class PropagationInfo {	// Propagated literal
private:
	WL wl;
	Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagated)
	Weight prevcertain, prevpossible; //values BEFORE the propagation was added

public:
    PropagationInfo(const Lit& l, const Weight& w, Occurrence t, const Weight& pc, const Weight& pv) :
    	wl(l, w), type(t), prevcertain(pc), prevpossible(pv) {}

    const Lit& 			getLit()	const { return wl.getLit(); }
    const Weight&		getWeight()	const { return wl.getWeight(); }
    const Occurrence& 	getType() 	const { return type; }
    const Weight& 		getPC()		const { return prevcertain; }
    const Weight& 		getPP()		const { return prevpossible; }
};


class Watch{
private:
			paggs 	agg;
			int 	index;
	const 	bool 	set;	//true if set literal, false if agg head
	const 	bool 	pos; 	//true if the literal occurs in the set, false if its negation is in the set
public:
	Watch(paggs agg, int index, bool set, bool pos):
		agg(agg), index(index), set(set), pos(pos){}

	virtual 	~Watch(){}

	paggs 		getAggComb() 	const { return agg; }
	int 		getIndex() 		const { return index; }
	void		setIndex(int i) 	  { index = i; }
	bool 		isSetLit() 		const { return set; }
	bool		isPos()			const { return pos; }
	Occurrence 	getType()		const { return !set?HEAD:pos?POS:NEG; }

	virtual WL	getWL()			const;
};

enum Expl{BASEDONCC,BASEDONCP,CPANDCC, HEADONLY};

struct AggReason {
private:
	const Agg&	expr;	//non-owning pointer
	const Lit	l;
	//const int 	index;
	const Expl	expl;
	const bool 	head;

public:
	AggReason(const Agg& agg, const Lit& l, Expl expl, bool head = false)
		:expr(agg), l(l), expl(expl), head(head){

	}

	const Agg&	getAgg() 		const	{ return expr; }
    const Lit&	getLit() 		const	{ return l; }
    //const int	getIndex() 		const	{ return index; }
    bool		isHeadReason() 	const	{ return head; }
    Expl		getExpl() 		const	{ return expl; }
};


class AggT{
public:
	virtual const char*	getName() const = 0;
	virtual AggrType 	getType() const = 0;
	virtual bool 		isNeutralElement	(const Weight& w) const = 0;
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) 	const = 0;
};

class MaxAggT: virtual public AggT{
public:
	virtual const char* getName() const { return "MAX"; }
	virtual AggrType 	getType() const { return MAX; }
	virtual bool 		isNeutralElement	(const Weight& w) const { return false; }
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) 	const;
};

class SPAggT: virtual public AggT{
public:
	virtual Weight		add		(const Weight& lhs, const Weight& rhs) 	const = 0;
	virtual Weight		remove	(const Weight& lhs, const Weight& rhs) 	const = 0;
};

class ProdAggT: virtual public SPAggT{
public:
	virtual const char* getName() const { return "PROD"; }
	virtual AggrType 	getType() const { return PROD; }
	virtual bool 		isNeutralElement(const Weight& w) const { return w==1; }
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) 	const;
	virtual Weight		add		(const Weight& lhs, const Weight& rhs) 	const;
	virtual Weight		remove	(const Weight& lhs, const Weight& rhs) 	const;
};

class SumAggT: virtual public SPAggT{
public:
	virtual const char* getName() const { return "SUM"; }
	virtual AggrType 	getType() const { return SUM; }
	virtual bool 		isNeutralElement(const Weight& w) const { return w==0; }
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) 	const;
	virtual Weight		add		(const Weight& lhs, const Weight& rhs) 	const;
	virtual Weight		remove	(const Weight& lhs, const Weight& rhs) 	const;
};

class CardAggT: virtual public SPAggT{
public:
	virtual AggrType	getType				() const { return CARD; }
	virtual const char* getName				() const { return "CARD"; }
	virtual bool 		isNeutralElement	(const Weight& w) 				const { return w==0; }
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) 	const { return true; }
	virtual Weight		add		(const Weight& lhs, const Weight& rhs) 	const;
	virtual Weight		remove	(const Weight& lhs, const Weight& rhs) 	const;
};


class CalcAgg: virtual public AggT{
protected:
	vpagg	aggregates;	//does OWN the pointers
	pset 	set;		//does OWN pointer
	paggsol	aggsolver;	//does NOT own this pointer
	Weight 	emptysetvalue;

	Propagator* prop;	//does OWN pointer

public:
	CalcAgg(const paggsol& solver, const vwl& wl);
	virtual ~CalcAgg();

	const paggsol&	getSolver		()			const	{ return aggsolver; }

	const pset &	getSet			()			const	{ return set; }
	const vwl&		getWL			()			const 	{ return set->getWL(); }
	const vpagg&	getAgg			() 			const	{ return aggregates; }
		vpagg&		getRefAgg		() 					{ return aggregates; }
	void 			addAgg			(pagg aggr);

	const Weight& 	getESV			() 			const 	{ return emptysetvalue; }
	void 			setESV			(const Weight& w)	{ emptysetvalue = w; }

	virtual Weight 	getBestPossible	() 			const 	= 0;

	void 			setProp			(Propagator* p) 	{ prop = p; }
	Propagator*		getProp			() 			const { return prop; }

	///////
	// INITIALIZATION
	///////
	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 */
			void 	doSetReduction			();
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const 	= 0;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 				= 0;

	void 			initialize(bool& unsat, bool& sat);

	///////
	// SEARCH
	///////
	virtual bool canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;
	// Propagate set literal
	rClause 	propagate		(const Lit& p, pw w);
	// Propagate head
	rClause 	propagate		(const Agg& agg);
	// Backtrack set literal
	void 		backtrack		(const Watch& w) ;
	// Backtrack head
	void 		backtrack		(const Agg& agg);

	void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) const;
};

class MaxCalc: public CalcAgg, virtual public MaxAggT{
public:
	MaxCalc(const paggsol& solver, const vwl& wl);
	virtual ~MaxCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;

	bool 		canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPCalc: public CalcAgg, virtual public SPAggT{
public:
	SPCalc(const paggsol& solver, const vwl& wl);
	virtual ~SPCalc() {}
	bool 		canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SumCalc: public SPCalc, virtual public SumAggT{
public:
	SumCalc(const paggsol& solver, const vwl& wl);
	virtual ~SumCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;
};

class ProdCalc: public SPCalc, virtual public ProdAggT{
public:
	ProdCalc(const paggsol& solver, const vwl& wl);
	virtual ~ProdCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;
};

class CardCalc: public SPCalc, virtual public CardAggT{
public:
	CardCalc(const paggsol& solver, const vwl& wl);
	virtual ~CardCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;
};


class Propagator {
protected:
	aggs * const agg;	//NON owning pointer
public:
	Propagator(paggs agg);
	virtual ~Propagator(){};

	// Propagate set literal
	virtual rClause 	propagate		(const Lit& p, Watch* w) = 0;
	// Propagate head
	virtual rClause 	propagate		(const Agg& agg) = 0;
	// Backtrack set literal
	virtual void 		backtrack		(const Watch& w) = 0;
	// Backtrack head
	virtual void 		backtrack		(const Agg& agg) = 0;

    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) 	const = 0;

    		aggs& 		as	() 	const 	{ return *agg; }
    		paggs 		asp	() 	const 	{ return agg; }
    	const aggs& 	asc	() 	const 	{ return *agg; }

    		lbool 		value(Lit l) const;

    virtual void initialize(bool& unsat, bool& sat);
};

void printAgg(aggs const * const c, bool printendline = false);
void printAgg(const Agg& c, bool printendline = false);

///////
// ID support
///////
bool 	oppositeIsJustified		(const WL& wl, vec<int>& currentjust, bool real, paggsol solver);
bool 	isJustified				(const WL& wl, vec<int>& currentjust, bool real, paggsol solver);
bool 	isJustified				(Var x, vec<int>& currentjust);

}

#endif /* AGGCOMB_HPP_ */
