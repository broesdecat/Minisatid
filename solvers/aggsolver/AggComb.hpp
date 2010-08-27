/*
 * AggComb.hpp
 *
 *  Created on: Aug 26, 2010
 *      Author: broes
 */

#ifndef AGGCOMB_HPP_
#define AGGCOMB_HPP_

#include "solvers/utils/Utils.hpp"

class AggSolver;
typedef AggSolver* paggsol;

class WL;
#include <vector>
typedef vector<Weight> vw;
typedef vector<Lit> vl;
typedef vector<WL> vwl;

namespace Aggrs{

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

class Agg;
class AggSet;
class PropagationInfo;
typedef Agg* pagg;
typedef vector<Agg*> vpagg;
typedef AggSet* pset;

class AggComb;
typedef AggComb* pcomb;

typedef vector<PropagationInfo> vprop;

class AggSet{
private:
	vwl	wlits;

public:
    AggSet(const vector<Lit>& lits, const vector<Weight>& weights);

    const vwl& getWL(){return wlits;}

    void setWL(const vector<WL>& newset){
    	wlits.clear();
		wlits.insert(wlits.begin(), newset.begin(), newset.end());
		//important to sort again to guarantee that it is sorted according to the weights
		std::sort(wlits.begin(), wlits.end());
    }
};

struct Agg{
	Weight		bound;
	Bound 		sign;
	Lit			head;
	HdEq		sem;

	Agg(const Weight& bound, Bound sign, const Lit& head, HdEq sem):
		bound(bound), sign(sign), head(head), sem(sem){	}

	const Lit& getHead(){ return head; }
};

class Watch{
private:
	AggComb* agg;
	const int index;
	const bool set;	//true if set literal, false if agg head
public:
	Watch(AggComb* agg, int index, bool set):
		agg(agg), index(index), set(set){}

	virtual ~Watch(){}

	AggComb* getAggComb() const { return agg; }
	int getIndex() const { return index; }
	bool isSetLit() const { return set; }
};

enum Expl{BASEDONCC,BASEDONCP,CPANDCC, HEADONLY};

struct AggReason {
private:
	const pcomb	expr;	//non-owning pointer
	const Lit	l;
	const int 	index;
	const Expl	expl;
	const bool 	head;

public:
	AggReason(pcomb, const Lit&, Expl, bool head = false);

	pcomb 		getAgg() 		const	{ return expr; }
    const Lit&	getLit() 		const	{ return l; }
    const int	getIndex() 		const	{ return index; }
    bool		isHeadReason() 	const	{ return head; }
    Expl		getExpl() 		const	{ return expl; }
};


/*class AggRef{
	pcomb c;
	int index;
};*/

class AggComb {
protected:
	vpagg	aggregates;	//does OWN the pointers
	pset 	set;	//does OWN pointer
	paggsol	aggsolver; //does NOT own this pointer

public:
	AggComb(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~AggComb(){
		deleteList<Agg>(aggregates);
		delete set;
	};

	const paggsol&		getSolver()			const	{ return aggsolver; }

	const pset &		getSet	()			const	{ return set; }
	const vwl&			getWL	()			const 	{ return set->getWL(); }
	const vpagg & 		getAgg	() 			const	{ return aggregates; }
	int 				addAgg	(pagg aggr)			{ aggregates.push_back(aggr); return aggregates.size()-1;}

	virtual AggrType	getType		() const = 0;
	virtual string 		getName		() const = 0;

    virtual rClause 	propagate	(Watch* w) = 0;
	virtual void 		backtrack	(Watch* w) = 0;

	virtual bool 		isMonotone	(const WL& l) = 0;

	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 * @remark: has to be called in the SUBCLASS constructors, because it needs the subclass data of which agg it is.
	 */
	virtual void 	doSetReduction() = 0;
	virtual pcomb 	initialize(bool& unsat);
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) 	const 	= 0;
	virtual WL 		handleOccurenceOfBothSigns(const WL& one, const WL& two) 		= 0;

	virtual void 	getExplanation(vec<Lit>& lits, AggReason* ar) const;

	///////
	// ID support
	///////
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;
	virtual bool 	oppositeIsJustified	(int elem, vec<int>& currentjust, bool real) const;
	virtual bool 	isJustified			(int elem, vec<int>& currentjust, bool real) const;
	virtual bool 	isJustified			(Var x, vec<int>& currentjust) const;
};


class PWAgg: public AggComb {
private:
	vpagg	aggregates;	//does NOT own the pointers
	pset 	set;	//does NOT own pointer
	paggsol	aggsolver; //does NOT own this pointer

public:
	PWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~PWAgg(){};
};


class FWAgg: public AggComb {
protected:
	string 	name;
	vprop 	stack;		// Stack of propagations of this expression so far.
	vector<lbool> truth;
	Weight 	currentbestcertain, currentbestpossible, emptysetvalue;
					//current keeps the currently derived min and max bounds
public:
	FWAgg(const paggsol& solver, const vector<Lit>& lits, const vector<Weight>& weights);
	virtual ~FWAgg(){};

	virtual pcomb 	initialize(bool& unsat);
	virtual lbool 	initialize(pagg agg);
	virtual void 	doSetReduction();

	virtual rClause propagate	(Watch* ws);
    virtual void 	backtrack	(int index);

	virtual Weight 	getBestPossible() 				const 	= 0;
	virtual void 	addToCertainSet(const WL& l) 			= 0;
	virtual void 	removeFromPossibleSet(const WL& l)	= 0;

	virtual bool isNeutralElement(const Weight& w) = 0;

	virtual void 	getExplanation(pagg agg, vec<Lit>& lits, AggReason& ar) const;

	bool 			oppositeIsJustified	(const WL& l, vec<int>& currentjust, bool real) const;
	bool 			isJustified			(const WL& l, vec<int>& currentjust, bool real) const;
	bool 			isJustified			(Var x, vec<int>& currentjust) const;

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
	virtual bool	isNeutralElement(const Weight& w) const { return false; }

	string getName() const { return "MAX"; }
	AggrType getType() const { return MAX; }
};

void printAgg(AggComb const * const c);

}

#endif /* AGGCOMB_HPP_ */
