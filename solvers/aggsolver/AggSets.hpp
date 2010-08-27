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

#ifndef AGGSETS_H_
#define AGGSETS_H_

#include <limits.h>
#include <vector>
#include <set>
#include <iostream>

#include "solvers/aggsolver/AggTypes.hpp"

class AggSolver;
typedef AggSolver* pAggSolver;

namespace Aggrs{
class AggrWatch;

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
class AggSet{
protected:
	lsagg		aggregates;	//does NOT own the pointers
	lwlv 		wlits;
	pAggSolver	aggsolver; //the solver that handles this set

public:
    AggSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s);
    virtual ~AggSet(){}

	const lsagg & 					getAgg	() 			const	{ return aggregates; }
	void 							addAgg	(pAgg aggr)			{ aggregates.push_back(aggr); }
	const lwlv & 					getWL	() 			const 	{ return wlits; }

    pAggSolver						getSolver()			const	{ return aggsolver; }

    virtual rClause propagate	(const Lit& p, const AggrWatch& ws) = 0;
	virtual void 	backtrack	(int index) = 0;

    virtual string 	getName() const = 0;
    virtual pSet 	initialize	(bool& unsat) = 0;	// Returns false if any involved aggregate is certainly UNSAT
    virtual void 	getExplanation(pAgg agg, vec<Lit>& lits, AggrReason& ar) const = 0;

    virtual Weight 			getBestPossible() 	const = 0;
    virtual const Weight& 	getCC() 			const = 0;
};

class AggrSet: public AggSet {
protected:
	string 	name;
	lprop 	stack;		// Stack of propagations of this expression so far.
	Weight 	currentbestcertain, currentbestpossible, emptysetvalue;
					//current keeps the currently derived min and max bounds

public:
    AggrSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s);
    virtual ~AggrSet(){}

	virtual rClause propagate	(const Lit& p, const AggrWatch& ws);
    virtual void 	backtrack	(int index);

	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 * @remark: has to be called in the SUBCLASS constructors, because it needs the subclass data of which agg it is.
	 */
	void 			doSetReduction();
	virtual pSet 	initialize(bool& unsat);
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) 	const 	= 0;
	virtual WLit 	handleOccurenceOfBothSigns(const WLit& one, const WLit& two) 		= 0;

	virtual Weight 	getBestPossible() 				const 	= 0;
	virtual void 	addToCertainSet(const WLit& l) 			= 0;
	virtual void 	removeFromPossibleSet(const WLit& l)	= 0;

	virtual void 	getExplanation(pAgg agg, vec<Lit>& lits, AggrReason& ar) const;

	///////
	// ID support
	///////

	bool 			oppositeIsJustified	(const WLV& elem, vec<int>& currentjust, bool real) const;
	bool 			isJustified			(const WLV& elem, vec<int>& currentjust, bool real) const;
	bool 			isJustified			(Var x, vec<int>& currentjust) const;

	///////
	// GETTERS - SETTERS
	///////
	string 							getName	() 					const 	{ return name; }
	const Weight& 					getESV	() 					const 	{ return emptysetvalue; }
	void 							setESV	(const Weight& w)			{ emptysetvalue = w; }
	const Weight& 					getCP	() 					const 	{ return currentbestpossible; }
	void 							setCP	(const Weight& w) 			{ currentbestpossible = w; }
	const Weight& 					getCC	() 					const 	{ return currentbestcertain; }
	void 							setCC	(const Weight& w) 			{ currentbestcertain = w; }

	const lprop &					getStack() 			const 	{ return stack; }

	virtual bool					isNeutralElement(const Weight& w) const = 0;
};

class AggrMaxSet: public AggrSet{
private:
	vector<MaxAgg*>	aggregates;		//does NOT own the pointers

public:
	AggrMaxSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s);
	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two);
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WLit& l);
	virtual void 	removeFromPossibleSet		(const WLit& l);

	MaxAgg*			getAgg(const vector<void*>::size_type& i) const	{ return aggregates[i];	}
	void 							addAgg(MaxAgg* aggr)		{ aggregates.push_back(aggr); }
	vector<void*>::size_type 							nbAgg() 			const	{ return aggregates.size(); }
	virtual bool	isNeutralElement(const Weight& w) const { return false; }
};

class AggrSPSet: public AggrSet{
public:
	AggrSPSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s);

	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two) 			  = 0;
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WLit& l);
	virtual void 	removeFromPossibleSet		(const WLit& l);
	virtual Weight	add							(const Weight& lhs, const Weight& rhs)	const = 0;
	virtual Weight	remove						(const Weight& lhs, const Weight& rhs) 	const = 0;

	virtual bool	isNeutralElement(const Weight& w) const = 0;
};

class AggrSumSet: public AggrSPSet{
private:
	vector<SumAgg*>	aggregates;		//does NOT own the pointers

public:
	AggrSumSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s);

	virtual pSet 	initialize(bool& unsat);

	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two);
	virtual Weight	add							(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove						(const Weight& lhs, const Weight& rhs) const;

	SumAgg*			getAgg(const vector<void*>::size_type& i) const	{ return aggregates[i]; }
	void 							addAgg(SumAgg* aggr)		{ aggregates.push_back(aggr); }
	vector<void*>::size_type 							nbAgg() 			const	{ return aggregates.size(); }
	virtual bool	isNeutralElement(const Weight& w) const { return w==0; }
};

class AggrProdSet: public AggrSPSet{
private:
	vector<ProdAgg*>	aggregates;		//does NOT own the pointers

public:
	AggrProdSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s);

	virtual pSet 	initialize(bool& unsat);

	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two);
	virtual Weight	add							(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove						(const Weight& lhs, const Weight& rhs) const;

	ProdAgg*			getAgg(const vector<void*>::size_type& i) const	{ return aggregates[i]; }
	void 							addAgg(ProdAgg* aggr)		{ aggregates.push_back(aggr); }
	vector<void*>::size_type 							nbAgg() 			const	{ return aggregates.size(); }
	virtual bool	isNeutralElement(const Weight& w) const { return w==1; }
};

class AggrCardSet: public AggSet{
	vector<Lit> watched, nonwatched; //disjoint watched and non-watched set
	int numberm, numberam;	//the number of mono/anti-mono literals to watch (depends on head or not, lb or not, ...)
	bool ws; //indicates whether we are using watched sets or not

	AggrCardSet(const vec<Lit>& lits, const vector<Weight>& weights, pAggSolver s): AggSet(lits, weights, s){}
	~AggrCardSet(){}

	virtual pSet 	initialize	(bool& unsat);
	virtual rClause propagate	(const Lit& l, bool& removewatch);
	virtual void 	backtrack	(int index){}
};

class AggrWatch {
private:
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    pSet		set;		//does NOT own the pointer
    int			index;

public:
    AggrWatch(pSet e, int i, Occurrence t) : type(t), set(e), index(i) {}

    Occurrence 	getType() 	const 	{ return type; }
    int 		getIndex() 	const 	{ return index; }
    pSet 		getSet() 	const	{ return set; }
};

void printAggrSet(pSet, bool);
}

#endif /* AGGSETS_H_ */
