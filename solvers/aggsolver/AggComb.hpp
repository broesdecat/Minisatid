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
    AggSet(const vector<Lit>& lits, const vector<Weight>& weights);

    const 	vwl& 	getWL()							{return wlits;}
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
			void 		setComb(AggComb* c, int ind) { comb = c; index = ind;	}
			AggComb* 	getAggComb() 		const 	{ return comb; }
			int			getIndex()			const	{ return index; }
			void 		setIndex(int ind) 			{ index = ind; }

	const 	Weight& getLowerBound()	const	{ return bound; }
	const 	Weight& getUpperBound()	const	{ return bound;}
			void	setLowerBound(const Weight& w)	{ bound = w;}
			void	setUpperBound(const Weight& w)	{ bound = w;}
			bool 	isLower()		const	{ return sign!=UPPERBOUND; }
			bool 	isUpper()		const	{ return sign!=LOWERBOUND; }
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


class AggComb {
protected:
	vpagg	aggregates;	//does OWN the pointers
	pset 	set;		//does OWN pointer
	paggsol	aggsolver;	//does NOT own this pointer

public:
	AggComb(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~AggComb();

	const paggsol&		getSolver()			const	{ return aggsolver; }

	const pset &		getSet	()			const	{ return set; }
	const vwl&			getWL	()			const 	{ return set->getWL(); }
	const vpagg & 		getAgg	() 			const	{ return aggregates; }
	void 				addAgg	(pagg aggr)			{ aggregates.push_back(aggr); aggr->setComb(this, aggregates.size()-1); }

	virtual AggrType	getType				() const = 0;
	virtual string 		getName				() const = 0;

	// Propagate set literal
	virtual rClause 	propagate			(const Lit& p, const Watch& w) = 0;
	// Propagate head
	virtual rClause 	propagate			(const Agg& agg, bool headtrue) = 0;
	// Backtrack set literal
	virtual void 		backtrack			(const Watch& w) = 0;
	// Backtrack head
	virtual void 		backtrack			(const Agg& agg) = 0;
    virtual void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) 	const = 0;

    // @pre: l is always IN the aggregate set TODO check this!
	virtual bool 		isMonotone			(const Agg& agg, const WL& l) const = 0;

	///////
	// INITIALIZATION
	///////
	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 */
	virtual void 	doSetReduction			();
	virtual pcomb 	initialize				(bool& unsat) 									= 0;
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight		(const Weight& one, const Weight& two) 	const 	= 0;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 				= 0;

	///////
	// ID support
	///////
	virtual bool 	canJustifyHead			(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;
	virtual bool 	oppositeIsJustified		(const WL& wl, vec<int>& currentjust, bool real) const;
	virtual bool 	isJustified				(const WL& wl, vec<int>& currentjust, bool real) const;
	virtual bool 	isJustified				(Var x, vec<int>& currentjust) const;
};


class PWAgg: public AggComb {
private:

public:
	PWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~PWAgg(){};
};

class CardPWAgg: public PWAgg {
private:
	Weight emptysetvalue;

public:
	const Weight& 	getESV	() 					const 	{ return emptysetvalue; }
	void 			setESV	(const Weight& w)			{ emptysetvalue = w; }

	CardPWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~CardPWAgg(){};

	virtual AggrType	getType				() const { return CARD; }
	virtual string 		getName				() const { return "CARD"; }

	virtual rClause 	propagate			(const Lit& p, const Watch& w);
	virtual rClause 	propagate			(const Agg& agg, bool headtrue);
	virtual void 		backtrack			(const Watch& w) {}
	virtual void 		backtrack			(const Agg& agg) {}
    virtual void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) const;

	virtual bool 		isMonotone			(const Agg& agg, const WL& l) const { return true; }

	virtual pcomb 		initialize			(bool& unsat);
	virtual Weight 		getCombinedWeight	(const Weight& one, const Weight& two) 	const;
	virtual WL 			handleOccurenceOfBothSigns(const WL& one, const WL& two);

	virtual bool 		canJustifyHead		(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};


class FWAgg: public AggComb {
protected:
	vprop 	stack;		// Stack of propagations of this expression so far.
	vector<lbool> truth, headvalue;
	vector<int> headindex;
	vector<bool> nomoreprops, optimagg;

	mutable vector<int> headproptime;
	mutable vector<bool> headprop;

	Weight 	currentbestcertain, currentbestpossible, emptysetvalue;
					//current keeps the currently derived min and max bounds
public:
	FWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~FWAgg(){};

	virtual pcomb 	initialize(bool& unsat);
	virtual lbool 	initialize(const Agg& agg);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead(const Agg& agg, const Weight& CC, const Weight& CP) const;

	virtual rClause propagate	(const Lit& p, const Watch& ws);
	virtual rClause propagate(const Agg& agg, bool headtrue);
	virtual void 	getExplanation(vec<Lit>& lits, const AggReason& ar) const;
	virtual void 	backtrack	(const Watch& w);
	virtual void 	backtrack	(const Agg& agg);
	virtual void 	backtrack	(const Agg& agg, int stacksize);

	virtual Weight 	getBestPossible() 				const 	= 0;
	virtual void 	addToCertainSet(const WL& l) 			= 0;
	virtual void 	removeFromPossibleSet(const WL& l)		= 0;

	///////
	// GETTERS - SETTERS
	///////
	const Weight& 	getESV	() 					const 	{ return emptysetvalue; }
	void 			setESV	(const Weight& w)			{ emptysetvalue = w; }
	const Weight& 	getCP	() 					const 	{ return currentbestpossible; }
	void 			setCP	(const Weight& w) 			{ currentbestpossible = w; }
	const Weight& 	getCC	() 					const 	{ return currentbestcertain; }
	void 			setCC	(const Weight& w) 			{ currentbestcertain = w; }

	const vprop&	getStack() 					const 	{ return stack; }
};

class MaxFWAgg: public FWAgg {
public:
	MaxFWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~MaxFWAgg(){};

	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual WL	 	handleOccurenceOfBothSigns	(const WL& one, const WL& two);
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WL& l);
	virtual void 	removeFromPossibleSet		(const WL& l);
	virtual bool 	isMonotone					(const Agg& agg, const WL& w) const;

	string 		getName() const { return "MAX"; }
	AggrType 	getType() const { return MAX; }

	virtual rClause propagate	(const Agg& agg, bool headtrue);
	virtual rClause propagateAll(const Agg& agg, bool headtrue);

	virtual bool 	canJustifyHead				(const Agg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

void printAgg(AggComb const * const c, bool printendline = false);
void printAgg(const Agg& c);

bool isNeutralElement(const Weight& w, AggrType t);

}

#endif /* AGGCOMB_HPP_ */
