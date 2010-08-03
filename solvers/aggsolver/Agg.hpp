//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
Copyright (c) 2006-2009, Maarten Mariën

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef AGG_H_
#define AGG_H_

#include <limits>
#include <vector>
#include <set>
#include <iostream>

#include "solvers/aggsolver/AggTypes.hpp"

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
	    head(head), headindex(-1), headvalue(l_Undef), set(set),
	    nomoreprops(false), optimagg(false), headprop(false), headproptime(-1){
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

	lbool 	initialize(); //throws UNSAT
	void 	backtrackHead();
	void	backtrack(int stacksize);
	rClause	propagateHead(const Lit& p);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead(const Weight& CC, const Weight& CP) const;

    virtual rClause propagate		(bool headtrue) = 0;
    virtual rClause propagateHead	(bool headtrue) = 0;

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

    virtual rClause propagate		(bool headtrue);
    virtual rClause propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPAgg: public Agg {
public:
	SPAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		Agg(bounds, bound, head, set){
	};

    virtual rClause propagate		(bool headtrue);
    virtual rClause propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;

	virtual Weight	add(const Weight& lhs, const Weight& rhs) const = 0;
	virtual Weight	remove(const Weight& lhs, const Weight& rhs) const = 0;
};

class SumAgg: public SPAgg {
public:
	SumAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SPAgg(bounds, bound, head, set){};

	virtual void	getMinimExplan(vec<Lit>& lits);

	virtual Weight	add(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

class CardAgg:public SumAgg{
public:
	CardAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SumAgg(bounds, bound, head, set){};

    virtual rClause propagate		(bool headtrue);
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SPAgg(bounds, bound, head, set){
	}

	virtual Weight	add(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

enum Expl{BASEDONCC,BASEDONCP,CPANDCC, HEADONLY};

class AggrReason {
private:
	pAgg		expr;		//does NOT own the pointer
	int 		index;
	Expl		expl;
	bool 		head;

public:
	AggrReason(pAgg, Expl, bool head = false);

    pAgg 		getAgg() 	const	{ return expr; }
    int 		getIndex() 	const	{ return index; }
    bool		isHeadReason() const{ return head; }
    Expl		getExpl() const		{ return expl; }
};

void printAggrSet(pSet, bool);
void printAggrExpr(pAgg);

}

#endif /* AGG_H_ */
