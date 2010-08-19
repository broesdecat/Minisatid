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

//Aggregate Data structure
struct AggDS{
	Weight		bound;
	Bound 		sign;
	Lit			head;

	pSet	 	set;		//non-owning pointer

	AggDS(const Weight& bound, Bound sign, const Lit& head, const pSet& set):
		bound(bound), sign(sign), head(head), set(set){	}

};

class Agg{
private:
	int			headindex;	//the index in the stack when this was derived
	lbool		headvalue;

protected:
	AggDS		agg;

	bool 		nomoreprops, optimagg;//indicates that this aggregate is always true, so no more propagation is necessary
	mutable bool headprop;
	mutable int	headproptime; //stack size at first moment where head can be propagated.

public:

    Agg(const Bound& bounds, const Weight& bound, const Lit& head, const pSet& set) :
	    agg(bound, bounds, head, set),
	    headindex(-1), headvalue(l_Undef),
	    nomoreprops(false), optimagg(false), headprop(false), headproptime(-1){
    }

    virtual ~Agg(){}

    /**
     * GET-SET METHODS
     */
    const 	Weight& getLowerBound()	const	{ return agg.bound; }
    const 	Weight& getUpperBound()	const	{ return agg.bound;}
    		void	setLowerBound(const Weight& w)	{ agg.bound = w;}
    		void	setUpperBound(const Weight& w)	{ agg.bound = w;}
			bool 	isLower()		const	{ return agg.sign!=UPPERBOUND; }
			bool 	isUpper()		const	{ return agg.sign!=LOWERBOUND; }
	const 	Lit& 	getHead()		const	{ return agg.head; }
	const 	lbool& 	getHeadValue() 	const	{ return headvalue; }
			int 	getHeadIndex() 	const	{ return headindex; }
	const	pSet&	getSet()	 	const	{ return agg.set; }

			void 	addAggToSet();

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

	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;

	void			setOptimAgg() { optimagg = true; }

	virtual bool 	isMonotone(const WLV& l) const = 0;
			bool 	aggValueImpliesHead(const Weight& w) const { return isLower()?w<=getLowerBound():w>=getUpperBound();}
};

class MaxAgg: public Agg {
public:
	MaxAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		Agg(bounds, bound, head, set){
	};

    virtual rClause propagate		(bool headtrue);
    virtual rClause propagateHead	(bool headtrue);

	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;

	virtual bool 	isMonotone(const WLV& l) const;
};

class SPAgg: public Agg {
public:
	SPAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		Agg(bounds, bound, head, set){
	};

    virtual rClause propagate		(bool headtrue);
    virtual rClause propagateHead	(bool headtrue);

	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;

	virtual bool 	isMonotone(const WLV& l) const = 0;

protected:
	virtual Weight	add(const Weight& lhs, const Weight& rhs) const = 0;
	virtual Weight	remove(const Weight& lhs, const Weight& rhs) const = 0;
};

class SumAgg: public SPAgg {
public:
	SumAgg(Bound bounds, Weight bound, Lit head, const pSet& set):
		SPAgg(bounds, bound, head, set){};

	void	getMinimExplan(vec<Lit>& lits);
	void 	addToBounds(const Weight& w);

	virtual bool 	isMonotone(const WLV& l) const;

protected:
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

	virtual bool 	isMonotone(const WLV& l) const;

protected:
	virtual Weight	add(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove(const Weight& lhs, const Weight& rhs) const;
};

enum Expl{BASEDONCC,BASEDONCP,CPANDCC, HEADONLY};

struct AggrReason {
private:
	const pAgg	expr;	//non-owning pointer
	const Lit	l;
	const int 	index;
	const Expl	expl;
	const bool 	head;

public:
	AggrReason(pAgg, const Lit&, Expl, bool head = false);

    pAgg 		getAgg() 		const	{ return expr; }
    const Lit&	getLit() 		const	{ return l; }
    const int	getIndex() 		const	{ return index; }
    bool		isHeadReason() 	const	{ return head; }
    Expl		getExpl() 		const	{ return expl; }
};

void printAggrExpr(const Agg*);

}

#endif /* AGG_H_ */
