#ifndef AGG_H_
#define AGG_H_

#include <limits>
#include <vector>
#include <set>
#include <iostream>

#include "AggTypes.h"
#include "Vec.h"

namespace Aggrs{

class Agg;
class AggrSet;

typedef Agg* pAgg;
typedef AggrSet* pSet;

typedef vector<pAgg> lsagg;
class AggrReason;

/**
 * The certain values contain info about the elements of the set that are currently CERTAINLY in the set (by their
 * truth value).
 * The possible values contain info about all elements that eventually MIGHT still be in the set (by their truth value).
 *
 * An aggregate is (currently) always a definition, so its head is always a positive literal.
 */

enum Bound {UPPERBOUND, LOWERBOUND/*, BOTHBOUNDS*/};

class Agg{
private:
	//Ready for possible future extensions to also allow double bounded aggregates.
	Weight		bound/*, boundupper*/;
	Bound 		bounds;
	Lit			head;
	int			headindex;	//the index in the stack when this was derived
	lbool		headvalue;

	pSet	 	set;		//does NOT own the pointer

protected:
	bool 		nomoreprops, optimagg;//indicates that this aggregate is always true, so no more propagation is necessary
	mutable bool headprop;
	mutable int	headproptime; //stack size at first moment where head can be propagated.

public:

    Agg(Bound bounds, Weight bound, Lit head, const pSet& set) :
	    bound(bound), bounds(bounds),
	    nomoreprops(false), optimagg(false), headprop(false), headproptime(-1),
	    head(head), headindex(-1), headvalue(l_Undef), set(set){
    }

    virtual ~Agg(){}

    /**
     * GET-SET METHODS
     */
    const 	Weight& getLowerBound()	const	{ return bound; }
    const 	Weight& getUpperBound()	const	{ return bound;/*bounds==BOTHBOUNDS?bound:boundupper; */}
    void			setLowerBound(Weight w)	{ bound = w;}
    void			setUpperBound(Weight w)	{ bound = w; /* bounds==BOTHBOUNDS?bound=w:boundupper = w;*/}
			bool 	isLower()		const	{ return bounds!=UPPERBOUND; }
			bool 	isUpper()		const	{ return bounds!=LOWERBOUND; }
	const 	Lit& 	getHead()		const	{ return head; }
	const 	lbool& 	getHeadValue() 	const	{ return headvalue; }
			int 	getHeadIndex() 	const	{ return headindex; }
			pSet	getSet()	 	const	{ return set; }

			void 	addAggToSet();

	void	addToBounds(const Weight& b){
		bound+=b;
		//boundupper+=b;
	}

	bool 	initialize();
	void 	backtrackHead();
	void	backtrack(int stacksize);
	Clause*	propagateHead(const Lit& p);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead(const Weight& CC, const Weight& CP) const;

    virtual Clause* propagate		(bool headtrue) = 0;
    virtual Clause* propagateHead	(bool headtrue) = 0;

    /**
     * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
     * which is equivalent with the clause bigvee{~l|l in L+} or p
     * and this is returned as the set {~l|l in L+}
     */
    virtual void	getExplanation	(vec<Lit>& lits, AggrReason& ar) const;

			void 	becomesCycleSource(vec<Lit>& nj) const;
	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const = 0;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;

	void			setOptimAgg() { optimagg = true; }
};

class MaxAgg: public Agg {
public:
	MaxAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		Agg(bounds, bound, head, set){
	};

    virtual Clause* propagate		(bool headtrue);
    virtual Clause* propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPAgg: public Agg {
public:
	SPAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		Agg(bounds, bound, head, set){
	};

    virtual Clause* propagate		(bool headtrue);
    virtual Clause* propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;

	virtual Weight	add(const Weight& lhs, const Weight& rhs) const = 0;
	virtual Weight	remove(const Weight& lhs, const Weight& rhs) const = 0;
};

class SumAgg: public SPAgg {
public:
	SumAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SPAgg(bounds, bound, head, set){};

	void	getMinimExplan(vec<Lit>& lits);

	Weight	add(const Weight& lhs, const Weight& rhs) const;
	Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

class CardAgg:public SumAgg{
public:
	CardAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SumAgg(bounds, bound, head, set){};

    virtual Clause* propagate		(bool headtrue);
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SPAgg(bounds, bound, head, set){
	}

	Weight	add(const Weight& lhs, const Weight& rhs) const;
	Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

enum Expl{BASEDONCC,BASEDONCP,CPANDCC, HEADONLY};

class AggrReason {
private:
	pAgg		expr;		//does NOT own the pointer
	int 		index;
	Expl		expl;

public:
	AggrReason(pAgg e, Expl e, bool head = false);

    pAgg 		getAgg() 	const	{ return expr; }
    int 		getIndex() 	const	{ return abs(index); }
    bool		isHeadReason() const{ return index<0; }
    Expl		getExpl() const		{ return expl; }
};

void printAggrSet(pSet, bool);
void printAggrExpr(pAgg);

}

#endif /* AGG_H_ */
