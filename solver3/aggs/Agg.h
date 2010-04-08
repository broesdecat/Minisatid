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

class Agg{
protected:
	Weight		bound;
	bool 		lower;

	bool 		nomoreprops, optimagg;//indicates that this aggregate is always true, so no more propagation is necessary
	mutable bool headprop;
	mutable int	headproptime; //stack size at first moment where head can be propagated.

	Lit			head;
	int			headindex;	//the index in the stack when this was derived
	lbool		headvalue;

	pSet	 	set;		//does NOT own the pointer

public:

    Agg(bool lower, Weight bound, Lit head, const pSet& set) :
	    bound(bound), lower(lower),
	    nomoreprops(false), optimagg(false), headprop(false), headproptime(-1),
	    head(head), headindex(-1), headvalue(l_Undef), set(set){
    }

    virtual ~Agg(){}

    /**
     * GET-SET METHODS
     */
    const 	Weight& getBound()		const	{ return bound; }
			bool 	isLower()		const	{ return lower; }
	const 	Lit& 	getHead()		const	{ return head; }
	const 	lbool& 	getHeadValue() 	const	{ return headvalue; }
			int 	getHeadIndex() 	const	{ return headindex; }
			pSet	getSet()	 	const	{ return set; }

			void 	addAggToSet();

	void 	setBound(const Weight& b)	{ bound = b; }

	bool 	initialize();
	void 	backtrackHead();
	void	backtrack(int stacksize);
	Clause*	propagateHead(const Lit& p);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead() const;

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
	MaxAgg(bool lower, Weight bound, Lit head, const pSet& set):
		Agg(lower, bound, head, set){
	};

    virtual Clause* propagate		(bool headtrue);
    virtual Clause* propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPAgg: public Agg {
public:
	SPAgg(bool lower, Weight bound, Lit head, const pSet& set):
		Agg(lower, bound, head, set){
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
	SumAgg(bool lower, Weight bound, Lit head, const pSet& set):
		SPAgg(lower, bound, head, set){
	};

	void	getMinimExplan(vec<Lit>& lits);

	Weight	add(const Weight& lhs, const Weight& rhs) const;
	Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(bool lower, Weight bound, Lit head, const pSet& set):
		SPAgg(lower, bound, head, set){
	}

	Weight	add(const Weight& lhs, const Weight& rhs) const;
	Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

class AggrReason {
private:
	pAgg		expr;		//does NOT own the pointer
	int 		index;

public:
	AggrReason(pAgg e, bool head = false);

    pAgg 		getAgg() 	const	{ return expr; }
    int 		getIndex() 	const	{ return abs(index); }
    bool		isHeadReason() const{ return index<0; }
};

void printAggrSet(pSet, bool);
void printAggrExpr(pAgg);

}

#endif /* AGG_H_ */
