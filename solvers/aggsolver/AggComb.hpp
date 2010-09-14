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

    const 	vwl& 	getWL()							{return wlits;}
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

public:
	Agg(const Weight& bound, Bound sign, const Lit& head, HdEq sem):
		bound(bound), sign(sign), head(head), sem(sem), comb(NULL), index(-1){	}

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
			bool 	isLower()		const	{ return sign!=UPPERBOUND; }
			bool 	isUpper()		const	{ return sign!=LOWERBOUND; }

			bool 	isDefined()		const	{ return sem==DEF; }
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
	paggs agg;
	const 	int 	index;
	const 	bool 	set;	//true if set literal, false if agg head
	const 	bool 	pos; 	//true if the literal occurs in the set, false if its negation is in the set
public:
	Watch(paggs agg, int index, bool set, bool pos):
		agg(agg), index(index), set(set), pos(pos){}

	virtual 	~Watch(){}

	paggs 	getAggComb() 	const { return agg; }
	int 		getIndex() 		const { return index; }
	bool 		isSetLit() 		const { return set; }
	Occurrence 	getType()		const { return !set?HEAD:pos?POS:NEG; }
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
		vpagg&	getRefAgg			() 					{ return aggregates; }
	void 			addAgg			(pagg aggr);

	const Weight& 	getESV			() 			const 	{ return emptysetvalue; }
	void 			setESV			(const Weight& w)	{ emptysetvalue = w; }

	virtual Weight 	getBestPossible	() 			const 	= 0;

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

	paggs initialize(bool& unsat);

	///////
	// SEARCH
	///////
	bool 		canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
	// Propagate set literal
	rClause 	propagate		(const Lit& p, const Watch& w);
	// Propagate head
	rClause 	propagate		(const Agg& agg);
	// Backtrack set literal
	void 		backtrack		(const Watch& w) ;
	// Backtrack head
	void 		backtrack		(const Agg& agg);

	void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) const;
};

class MaxCalc: virtual public CalcAgg, virtual public MaxAggT{
public:
	MaxCalc(const paggsol& solver, const vwl& wl);
	virtual ~MaxCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;
};

class SumCalc: virtual public CalcAgg, virtual public SumAggT{
public:
	SumCalc(const paggsol& solver, const vwl& wl);
	virtual ~SumCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;
};

class ProdCalc: virtual public CalcAgg, virtual public ProdAggT{
public:
	ProdCalc(const paggsol& solver, const vwl& wl);
	virtual ~ProdCalc() {}
	virtual Weight 	getBestPossible			() 										const;
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 			;
};

class CardCalc: virtual public CalcAgg, virtual public CardAggT{
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

	virtual bool 		canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;

	// Propagate set literal
	virtual rClause 	propagate		(const Lit& p, const Watch& w) = 0;
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

    virtual paggs initialize(bool& unsat);
};

class PWAgg: public Propagator {
private:
	vector<Lit> nf, nfex, nt, ntex;
public:
	PWAgg(paggs agg);
	virtual ~PWAgg(){};

	virtual void 	backtrack		(const Watch& w) {}

	//Still assuming one aggregate!
	virtual paggs 	initialize(bool& unsat){
		/*
		 * First find nf and nfex:
		 * go over set, incrementally calc min and max value, by taking positive monotone set literals
		 * and negative anti-monotone ones. If satisfied, nf is finished.
		 * Then go over all in nf, remove them and add extra lits to nfex until satisfied again. Repeat
		 * for all in nf.
		 *
		 * Same for nt and ntex, but switch mono/am and until not-satisfied.
		 */

		/*
		 * Necessary methods: issatisfied(min, max, agg), is falsified(min, max, agg)
		 * calcmin(set), calcmax(set)
		 */
	}

	/*
	 * On propagation, do same to fill the sets again.
	 * For all literals in nt/nf for which no replacement can be found, they can be propagated as they
	 * occur in the set.
	 */
};

class CardPWAgg: public PWAgg, public virtual CardAggT {
private:

public:
	CardPWAgg(paggs agg);
	virtual ~CardPWAgg(){};

	virtual rClause propagate		(const Lit& p, const Watch& w);
	virtual rClause propagate		(const Agg& agg);
	virtual void 	backtrack		(const Agg& agg);
    virtual void 	getExplanation	(vec<Lit>& lits, const AggReason& ar) const;

	virtual paggs 	initialize		(bool& unsat);

	virtual bool 	canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};


class FWAgg: public Propagator {
protected:
	vprop 	stack;		// Stack of propagations of this expression so far.
	vector<lbool> truth, headvalue;
	vector<int> headindex;
	vector<bool> nomoreprops, optimagg;

	mutable vector<int> headproptime;
	mutable vector<bool> headprop;

	Weight 	currentbestcertain, currentbestpossible;
					//current keeps the currently derived min and max bounds
public:
	FWAgg(paggs agg);
	virtual ~FWAgg(){};

	virtual paggs 	initialize(bool& unsat);
	virtual lbool 	initialize(const Agg& agg);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const;

	virtual rClause propagate	(const Lit& p, const Watch& ws);

// TODO dit is lelijk, maar het verplicht om eerst de top propagate op te roepen en daarna pas de lagere, maar er zullen wel betere manieren zijn.
	virtual rClause propagate(const Agg& agg);
protected:
	virtual rClause propagate(const Agg& agg, bool headtrue) = 0;

public:
	virtual void 	getExplanation(vec<Lit>& lits, const AggReason& ar) const;
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

	virtual bool 	canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SumFWAgg: public  SPFWAgg, virtual public SumAggT{
public:
	SumFWAgg(paggs agg);
	virtual ~SumFWAgg(){};

	virtual paggs 	initialize	(bool& unsat);

			void	getMinimExplan		(const Agg& agg, vec<Lit>& lits);
			void 	addToBounds			(Agg& agg, const Weight& w);
};

class ProdFWAgg: public  SPFWAgg, virtual public ProdAggT {
public:
	ProdFWAgg(paggs agg);
	virtual ~ProdFWAgg(){};

	virtual paggs 	initialize	(bool& unsat);
};

class MaxFWAgg: public  FWAgg, virtual public MaxAggT {
public:
	MaxFWAgg(paggs agg);
	virtual ~MaxFWAgg(){};

	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);

	virtual rClause propagate	(const Agg& agg, bool headtrue);
	virtual rClause propagateAll(const Agg& agg, bool headtrue);

	virtual bool 	canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;

	virtual paggs 	initialize	(bool& unsat);
};

void printAgg(aggs const * const c, bool printendline = false);
void printAgg(const Agg& c);

///////
// ID support
///////
bool 	oppositeIsJustified		(const WL& wl, vec<int>& currentjust, bool real, paggsol solver);
bool 	isJustified				(const WL& wl, vec<int>& currentjust, bool real, paggsol solver);
bool 	isJustified				(Var x, vec<int>& currentjust);

}

#endif /* AGGCOMB_HPP_ */
