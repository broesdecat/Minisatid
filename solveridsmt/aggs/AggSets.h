#ifndef AGGSETS_H_
#define AGGSETS_H_

#include <limits.h>
#include <vector>
#include <set>
#include <iostream>

#include "AggTypes.h"
#include "Vec.h"

using namespace std;
using namespace boost;

class AggSolver;
typedef shared_ptr<AggSolver> pAggSolver;
typedef weak_ptr<AggSolver> wpAggSolver;

namespace Aggrs{

class Agg;
class AggrSet;

typedef weak_ptr<Agg> wpAgg;
typedef vector<wpAgg> lwagg;
typedef shared_ptr<AggrSet> pSet;
typedef weak_ptr<AggrSet> wpSet;

class AggrWatch;
typedef shared_ptr<AggrWatch> pWatch;
typedef weak_ptr<AggrWatch> wpWatch;

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
class AggrSet {
protected:
	string 	name;
	lwagg	aggregates;
	lwlv 	wlits;
	lprop 	stack;		// Stack of propagations of this expression so far.
	Weight 	currentbestcertain, currentbestpossible, emptysetvalue;
					//current keeps the currently derived min and max bounds
	wpAggSolver aggsolver; //the solver that handles this set

public:
    AggrSet(vec<Lit>& lits, vector<Weight>& weights, wpAggSolver s);

	void 			initialize();
	Clause* 		propagate(const Lit& p, const AggrWatch& ws);

    virtual void 	backtrack(int index);

	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 * @remark: has to be called in the SUBCLASS constructors, because it needs the subclass data of which agg it is.
	 */
	void 			doSetReduction();
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) 	const 	= 0;
	virtual WLit 	handleOccurenceOfBothSigns(const WLit& one, const WLit& two) 		= 0;

	virtual Weight 	getBestPossible() 				const 	= 0;
	virtual void 	addToCertainSet(const WLit& l) 			= 0;
	virtual void 	removeFromPossibleSet(const WLit& l)	= 0;

	bool 			oppositeIsJustified	(const WLV& elem, vec<int>& currentjust, bool real) const;
	bool 			isJustified			(const WLV& elem, vec<int>& currentjust, bool real) const;
	bool 			isJustified			(Var x, vec<int>& currentjust) const;

	/**
	 * GETTERS - SETTERS
	 */
	string 							getName() 			const 	{ return name; }
	const Weight& 					getEmptySetValue() 	const 	{ return emptysetvalue; }
	const Weight& 					getCP() 			const 	{ return currentbestpossible; }
	const Weight& 					getCC() 			const 	{ return currentbestcertain; }
	void 							setEmptySetValue(const Weight& w) { emptysetvalue = w; }
	void 							setCP(const Weight& w) 		{ currentbestpossible = w; }
	void 							setCC(const Weight& w) 		{ currentbestcertain = w; }

	lwagg::const_iterator 			getAggBegin() 		const	{ return aggregates.begin(); }
	lwagg::const_iterator 			getAggEnd() 		const	{ return aggregates.end(); }
	void 							addAgg(wpAgg aggr)			{ aggregates.push_back(aggr); }
	int 							nbAgg() 			const	{ return aggregates.size(); }

	lwlv::const_iterator 			getWLBegin() 		const 	{ return wlits.begin(); }
	lwlv::const_iterator 			getWLEnd()			const 	{ return wlits.end(); }
	lwlv::const_reverse_iterator 	getWLRBegin() 		const 	{ return wlits.rbegin(); }
	lwlv::const_reverse_iterator 	getWLREnd() 		const 	{ return wlits.rend(); }
	const WLV& 						operator[](int i) 	const 	{ return wlits[i]; }
	int 							size() 				const 	{ return wlits.size(); }

	int 							getStackSize() 		const 	{ return stack.size(); }
	const PropagationInfo 			getStackBack() 		const 	{ return stack.back(); }
	lprop::const_iterator 			getStackBegin() 	const 	{ return stack.begin(); }
	lprop::const_iterator 			getStackEnd()		const 	{ return stack.end(); }

	pAggSolver						getSolver()			const	{ return aggsolver.lock(); }
};

class AggrMaxSet: public AggrSet{
public:
	AggrMaxSet(vec<Lit>& lits, vector<Weight>& weights, weak_ptr<AggSolver> s):AggrSet(lits, weights, s){
		name = "MAX";
		//FIXME FIXME: moet eigenlijk een voorstelling van -infinity zijn
		//ik had eerst: |minimum van de set| -1, maar de bound kan NOG lager liggen, dus dan is het fout
		emptysetvalue = Weight(INT_MIN)-1;
	};

	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two);
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WLit& l);
	virtual void 	removeFromPossibleSet		(const WLit& l);
};

class AggrSPSet: public AggrSet{
public:
	AggrSPSet(vec<Lit>& lits, vector<Weight>& weights, weak_ptr<AggSolver> s):AggrSet(lits, weights, s){};

	virtual Weight 	getCombinedWeight			(const Weight& one, const Weight& two) 	const;
	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two) 			  = 0;
	virtual Weight 	getBestPossible				() 										const;
	virtual void 	addToCertainSet				(const WLit& l);
	virtual void 	removeFromPossibleSet		(const WLit& l);
	virtual Weight	add							(const Weight& lhs, const Weight& rhs)	const = 0;
	virtual Weight	remove						(const Weight& lhs, const Weight& rhs) 	const = 0;
};

class AggrSumSet: public AggrSPSet{
public:
	AggrSumSet(vec<Lit>& lits, vector<Weight>& weights, weak_ptr<AggSolver> s):AggrSPSet(lits, weights, s){
		name = "SUM";
		emptysetvalue = 0;
	};

	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two);
	virtual Weight	add							(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove						(const Weight& lhs, const Weight& rhs) const;
};

class AggrProdSet: public AggrSPSet{
public:
	AggrProdSet(vec<Lit>& lits, vector<Weight>& weights, weak_ptr<AggSolver> s):AggrSPSet(lits, weights, s){
		name = "PROD";
		emptysetvalue = 1;
	};

	virtual WLit 	handleOccurenceOfBothSigns	(const WLit& one, const WLit& two);
	virtual Weight	add							(const Weight& lhs, const Weight& rhs) const;
	virtual Weight	remove						(const Weight& lhs, const Weight& rhs) const;
};

class AggrWatch {
private:
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    wpSet		set;
    int			index;

public:
    AggrWatch(const wpSet& e, int i, Occurrence t) : type(t), set(e), index(i) {}

    Occurrence 	getType() 	const 	{ return type; }
    int 		getIndex() 	const 	{ return index; }
    pSet 		getSet() 	const	{ return set.lock(); }
};
}

#endif /* AGGSETS_H_ */
