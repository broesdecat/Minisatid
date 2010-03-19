#ifndef AGG_H_
#define AGG_H_

#include <limits>
#include <vector>
#include <set>
#include <iostream>

#include "AggSets.h"

using namespace std;
using namespace boost;

namespace Aggrs{

class Agg;
typedef shared_ptr<Agg> pAgg;
typedef weak_ptr<Agg> wpAgg;

typedef vector<pAgg> lsagg;
typedef vector<wpAgg> lwagg;

class AggrReason;
typedef shared_ptr<AggrReason> pReason;
typedef weak_ptr<AggrReason> wpReason;

/**
 * The certain values contain info about the elements of the set that are currently CERTAINLY in the set (by their
 * truth value).
 * The possible values contain info about all elements that eventually MIGHT still be in the set (by their truth value).
 *
 * An aggregate is (currently) always a definition, so its head is always a positive literal.
 */

class Agg: public enable_shared_from_this<Agg>{
protected:
	Weight		bound;
	bool 		lower;

	Lit			head;
	int			headindex;	//the index in the stack when this was derived
	lbool		headvalue;

	wpSet	 	set;

    virtual pAgg getAgg(){
        return shared_from_this();
    }

public:

    Agg(bool lower, Weight bound, Lit head, const wpSet& set) :
	    bound(bound), lower(lower), head(head), headindex(-1), headvalue(l_Undef), set(set) {
    }

    /**
     * GET-SET METHODS
     */
    const 	Weight& getBound()		const	{ return bound; }
			bool 	isLower()		const	{ return lower; }
	const 	Lit& 	getHead()		const	{ return head; }
	const 	lbool& 	getHeadValue() 	const	{ return headvalue; }
			int 	getHeadIndex() 	const	{ return headindex; }
			pSet	getSet()	 	const	{ return set.lock(); }

	void 	addAggToSet() 				{ set.lock()->addAgg(getAgg()); }

	void 	setBound(const Weight& b)	{ bound = b; }

	void 	initialize();
	void 	backtrackHead();
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
};

class MaxAgg: public Agg {
public:
	MaxAgg(bool lower, Weight bound, Lit head, const wpSet& set):
		Agg(lower, bound, head, set){
	};

    virtual Clause* propagate		(bool headtrue);
    virtual Clause* propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPAgg: public Agg {
public:
	SPAgg(bool lower, Weight bound, Lit head, const wpSet& set):
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
	SumAgg(bool lower, Weight bound, Lit head, const wpSet& set):
		SPAgg(lower, bound, head, set){
	};

	void	getMinimExplan(vec<Lit>& lits);

	Weight	add(const Weight& lhs, const Weight& rhs) const;
	Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(bool lower, Weight bound, Lit head, const wpSet& set):
		SPAgg(lower, bound, head, set){
	}

	Weight	add(const Weight& lhs, const Weight& rhs) const;
	Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

class AggrReason {
private:
	wpAgg		expr;
	int 		index;

public:
	AggrReason(wpAgg e, bool head = false): expr(e), index(0) {
		index = e.lock()->getSet()->getStackSize();
		if(head==true){
			index = -index;
		}
    }

    pAgg 		getAgg() 	const	{ return expr.lock(); }
    int 		getIndex() 	const	{ return abs(index); }
    bool		isHeadReason() const{ return index<0; }
};
}

#endif /* AGG_H_ */
