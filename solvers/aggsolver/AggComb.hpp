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

	class AggComb;
	typedef AggComb* pcomb;

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

	AggComb* 	comb;
	int			index;

public:
	Agg(const Weight& bound, Bound sign, const Lit& head, HdEq sem):
		bound(bound), sign(sign), head(head), sem(sem), comb(NULL), index(-1){	}

	const 	Lit& 		getHead() 			const 	{ return head; }
			void 		setComb(AggComb* c, int ind){ comb = c; index = ind;	}
			AggComb* 	getAggComb() 		const 	{ return comb; }
			int			getIndex()			const	{ return index; }
			void 		setIndex(int ind) 			{ index = ind; }

	const 	Weight& getLowerBound()	const			{ return bound; }
	const 	Weight& getUpperBound()	const			{ return bound;}
			void	setLowerBound(const Weight& w)	{ bound = w;}
			void	setUpperBound(const Weight& w)	{ bound = w;}
			bool 	isLower()		const			{ return sign!=UPPERBOUND; }
			bool 	isUpper()		const			{ return sign!=LOWERBOUND; }

			bool 	isDefined()		const			{ return sem==DEF; }
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
protected:
			AggComb* agg;
	const 	int 	index;
	const 	bool 	set;	//true if set literal, false if agg head
	const 	bool 	pos; 	//true if the literal occurs in the set, false if its negation is in the set
public:
	Watch(AggComb* agg, int index, bool set, bool pos):
		agg(agg), index(index), set(set), pos(pos){}

	virtual 	~Watch(){}

	AggComb* 	getAggComb() 	const { return agg; }
	int 		getIndex() 		const { return index; }
	bool 		isSetLit() 		const { return set; }
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
	virtual bool 		isNeutralElement(const Weight& w) const = 0;
};

class MaxAggT: virtual public AggT{
public:
	virtual const char* getName() const { return "MAX"; }
	virtual AggrType 	getType() const { return MAX; }
	virtual bool 		isNeutralElement(const Weight& w) const { return false; }
};

class ProdAggT: virtual public AggT{
public:
	virtual const char* getName() const { return "PROD"; }
	virtual AggrType 	getType() const { return PROD; }
	virtual bool 		isNeutralElement(const Weight& w) const { return w==1; }
};

class SumAggT: virtual public AggT{
public:
	virtual const char* getName() const { return "SUM"; }
	virtual AggrType 	getType() const { return SUM; }
	virtual bool 		isNeutralElement(const Weight& w) const { return w==0; }
};

class CardAggT: virtual public AggT{
public:
	virtual AggrType	getType				() const { return CARD; }
	virtual const char* getName				() const { return "CARD"; }
	virtual bool 		isNeutralElement(const Weight& w) const { return w==0; }
};

class CalcAgg{
public:
	virtual Weight	add			(const Weight& lhs, const Weight& rhs) const = 0;
	virtual Weight	remove		(const Weight& lhs, const Weight& rhs) const = 0;
};

class SumCalc: virtual public CalcAgg{
public:
	virtual Weight	add			(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove		(const Weight& lhs, const Weight& rhs) const;
};

class ProdCalc: virtual public CalcAgg{
public:
	virtual Weight	add			(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove		(const Weight& lhs, const Weight& rhs) const;

};


class AggComb: virtual public AggT {
protected:
	vpagg	aggregates;	//does OWN the pointers
	pset 	set;		//does OWN pointer
	paggsol	aggsolver;	//does NOT own this pointer
	Weight 	emptysetvalue;

public:
	AggComb(const paggsol& solver, const vwl& wl);
	//AggComb(const AggComb& comb);
	virtual ~AggComb();

	const paggsol&		getSolver		()			const	{ return aggsolver; }

	const pset &		getSet			()			const	{ return set; }
	const vwl&			getWL			()			const 	{ return set->getWL(); }
	const vpagg & 		getAgg			() 			const	{ return aggregates; }
	virtual void 		addAgg			(pagg aggr);

	virtual Weight 		getBestPossible	() 			const 	= 0;
	virtual bool 		canJustifyHead	(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;

	const Weight& 		getESV			() 			const 	{ return emptysetvalue; }
	void 				setESV			(const Weight& w)	{ emptysetvalue = w; }

	// Propagate set literal
	virtual rClause 	propagate		(const Lit& p, const Watch& w) = 0;
	// Propagate head
	virtual rClause 	propagate		(const Agg& agg) = 0;
	// Backtrack set literal
	virtual void 		backtrack		(const Watch& w) = 0;
	// Backtrack head
	virtual void 		backtrack		(const Agg& agg) = 0;
    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) 	const = 0;

    // @pre: l is always IN the aggregate set TODO check this!
	virtual bool 		isMonotone		(const Agg& agg, const WL& l) const = 0;

	///////
	// INITIALIZATION
	///////
	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 */
	virtual void 	doSetReduction			();
	/**
	 * @remark: if the returned pointer is different to the original one, the original one should be DELETED!
	 */
	virtual pcomb 	initialize				(bool& unsat);
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const 	= 0;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 				= 0;
};


class PWAgg: public AggComb {
private:

public:
	PWAgg(const paggsol& solver, const vwl& wl);
	virtual ~PWAgg(){};
};

class CardPWAgg: public PWAgg, CardAggT, SumCalc {
private:
	int numberm, numberam;
	bool checkm, checkam;
	vector<WL> watchedm, restm, watchedam, restam;
public:
	CardPWAgg(const paggsol& solver, const vwl& wl);
	virtual ~CardPWAgg(){};

	virtual rClause 	propagate			(const Lit& p, const Watch& w);
	virtual rClause 	propagate			(const Agg& agg);
	virtual void 		backtrack			(const Watch& w) {}
	virtual void 		backtrack			(const Agg& agg);
    virtual void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) const;

	virtual bool 		isMonotone			(const Agg& agg, const WL& l) const { return true; }

	virtual pcomb 		initialize			(bool& unsat);
	virtual Weight 		getCombinedWeight	(const Weight& one, const Weight& two) 	const;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two);

	virtual Weight 	getBestPossible() const;
	virtual bool canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;

	const vector<WL>& 		getPosWatched() const	 { return watchedam; }
	const vector<WL>& 		getNegWatched() const	 { return watchedm; }
};

class PWWatch: public Watch{
public:
	PWWatch(CardPWAgg* agg, int index, bool set, bool pos):
			Watch(agg, index, set, pos){}

	virtual WL	getWL()			const;
};


class FWAgg: public AggComb {
protected:
	vprop 			stack;		// Stack of propagations of this expression so far.
	vector<lbool> 	truth, headvalue;
	vector<int> 	headindex;
	vector<bool> 	nomoreprops, optimagg; //If optimagg, no standard aggregate optimizations on the bounds should be used!

	mutable vector<int>		headproptime;
	mutable vector<bool>	headprop;

	Weight 			currentbestcertain, currentbestpossible;
					//current keeps the currently derived min and max bounds
public:
	FWAgg(const paggsol& solver, const vwl& wl);
	virtual ~FWAgg(){};

	virtual pcomb 	initialize(bool& unsat);
	virtual lbool 	initialize(const Agg& agg);

	void addOptimAgg(pagg agg){ addAgg(agg); optimagg[agg->getIndex()] = true;}

	virtual void 				addAgg			(pagg aggr);

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

class SPFWAgg: public FWAgg, virtual public CalcAgg {
public:
	SPFWAgg(const paggsol& solver, const vwl& wl);
	virtual ~SPFWAgg(){};

	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);

	virtual rClause propagate	(const Agg& agg, bool headtrue);
	virtual rClause propagateAll(const Agg& agg, bool headtrue);

	virtual bool canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SumFWAgg: public SPFWAgg, SumAggT, SumCalc{
public:
	SumFWAgg(const paggsol& solver, const vwl& wl);
	virtual ~SumFWAgg(){};

	virtual WL	 	handleOccurenceOfBothSigns	(const WL& one, const WL& two);
	virtual bool 	isMonotone					(const Agg& agg, const WL& w) const;

	virtual pcomb 	initialize	(bool& unsat);

			void	getMinimExplan		(const Agg& agg, vec<Lit>& lits);
			void 	addToBounds			(Agg& agg, const Weight& w);
};

class ProdFWAgg: public SPFWAgg, ProdCalc, ProdAggT {
public:
	ProdFWAgg(const paggsol& solver, const vwl& wl);
	virtual ~ProdFWAgg(){};

	virtual WL	 	handleOccurenceOfBothSigns	(const WL& one, const WL& two);
	virtual bool 	isMonotone					(const Agg& agg, const WL& w) const;

	virtual pcomb 	initialize	(bool& unsat);
};

class MaxFWAgg: public FWAgg, MaxAggT {
public:
	MaxFWAgg(const paggsol& solver, const vwl& wl);
	virtual ~MaxFWAgg(){};

	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual WL	 	handleOccurenceOfBothSigns	(const WL& one, const WL& two);
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);
	virtual bool 	isMonotone					(const Agg& agg, const WL& w) const;

	virtual rClause propagate	(const Agg& agg, bool headtrue);
	virtual rClause propagateAll(const Agg& agg, bool headtrue);

	virtual bool canJustifyHead(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

void printAgg(AggComb const * const c, bool printendline = false);
void printAgg(const Agg& c);

///////
// ID support
///////
bool 	oppositeIsJustified		(const WL& wl, vec<int>& currentjust, bool real, paggsol solver);
bool 	isJustified				(const WL& wl, vec<int>& currentjust, bool real, paggsol solver);
bool 	isJustified				(Var x, vec<int>& currentjust);

}

#endif /* AGGCOMB_HPP_ */
