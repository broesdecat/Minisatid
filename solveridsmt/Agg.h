#ifndef MINAGG_H_
#define MINAGG_H_

#include <limits>
#include <vector>
#include <set>
#include <iostream>

#include <boost/smart_ptr/shared_ptr.hpp>
#include <boost/smart_ptr/weak_ptr.hpp>
#include <boost/smart_ptr/enable_shared_from_this.hpp>

#include "Vec.h"
#include "SolverTypes.h"

using namespace std;
using namespace boost;

class Agg;
class MaxAgg;
class ProdAgg;
class SumAgg;
class AggrSet;

class WLV;
class PropagationInfo;

typedef vector<WLV> lwlv;
//typedef vector<Agg*> lagg;
typedef vector<shared_ptr<Agg> > lsagg;
typedef vector<weak_ptr<Agg> > lwagg;
typedef vector<PropagationInfo> lprop;

enum AggrType {SUM, PROD, MIN, MAX};
enum Occurrence {HEAD, POS, NEG};

class WLit {  // Weighted literal
private:
	Lit lit;
	Weight weight;

public:
    explicit WLit(const Lit& l, const Weight& w) : lit(l), weight(w) {}

    const Lit& 		getLit() 	const { return lit; }
    const Weight&	getWeight() const { return weight; }

    bool operator<	(const WLit& p)		 const { return weight < p.weight; }
    bool operator<	(const Weight& bound)const { return weight < bound; }
    bool operator==	(const WLit& p)		 const { return weight == p.weight && lit==p.lit; }
};

class WLV: public WLit{
private:
	lbool value;

public:
	explicit WLV(const Lit& l, const Weight& w, lbool value) : WLit(l, w), value(value) {}

	lbool	getValue() const 	{ return value; }
	void	setValue(lbool v) 	{ value = v; }
};

class PropagationInfo {	// Propagated literal
private:
	Lit 	lit;
	Weight 	weight;
	Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagate)
	Weight prevcertain, prevpossible; //values BEFORE the propagation was added

public:
    PropagationInfo(const Lit& l, const Weight& w, Occurrence t, const Weight& pc, const Weight& pv) :
    	lit(l), weight(w), type(t), prevcertain(pc), prevpossible(pv) {}

    const Lit& 			getLit()	const { return lit; }
    const Weight&		getWeight()	const { return weight; }
    const Occurrence& 	getType() 	const { return type; }
    const Weight& 		getPC()		const { return prevcertain; }
    const Weight& 		getPP()		const { return prevpossible; }
};

class AggrWatch {
private:
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    AggrSet*	set;
    int			index;

public:
    AggrWatch(AggrSet* e, int i, Occurrence t) : type(t), set(e), index(i) {}

    Occurrence 	getType() 	const 	{ return type; }
    int 		getIndex() 	const 	{ return index; }
    AggrSet* 	getSet() 	const	{ return set; }
};

class AggrReason {
private:
	weak_ptr<Agg>	expr;
	int 			index;

public:
    AggrReason(weak_ptr<Agg> e, int index) : expr(e), index(index) {}

    weak_ptr<Agg> 	getAgg() 	const { return expr; }
    int 			getIndex() 	const { return index; }
};

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
class AggrSet {
protected:
	Weight currentbestcertain, currentbestpossible, emptysetvalue;
				//current keeps the currently derived min and max bounds
	string name;

	lwagg	aggregates;
	lwlv 	wlits;
	lprop 	stack;		// Stack of propagations of this expression so far.

public:
    AggrSet(vec<Lit>& lits, vector<Weight>& weights):currentbestcertain(0),currentbestpossible(0),emptysetvalue(0){
    	for (int i = 0; i < lits.size(); i++) {
			wlits.push_back(WLV(lits[i], weights[i], l_Undef));
		}
		sort(wlits.begin(), wlits.end());
    };

	void 	initialize();
	Clause* propagate		(const Lit& p, const AggrWatch& ws);

    virtual void 	backtrack		(int index);
    virtual Clause* propagateBodies();

	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 * @remark: has to be called in the SUBCLASS constructors, because it needs the subclass data of which agg it is.
	 */
			void 	doSetReduction();
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) const = 0;
	virtual WLit 	handleOccurenceOfBothSigns(const WLit& one, const WLit& two) = 0;

	virtual Weight 	getBestPossible			() 		const 	= 0;
	virtual void 	initEmptySetValue		()		 		= 0;
	virtual void 	addToCertainSet			(const WLit& l) = 0;
	virtual void 	removeFromPossibleSet	(const WLit& l)	= 0;

	bool isJustified		(Var x, vec<int>& currentjust) const;
	bool isJustified		(const WLV& elem, vec<int>& currentjust, bool real) const;
	bool oppositeIsJustified(const WLV& elem, vec<int>& currentjust, bool real) const;

	/**
	 * GETTERS - SETTERS
	 */
	string getName() const { return name; }
	const Weight& getEmptySetValue() const { return emptysetvalue; }
	const Weight& getCP() const { return currentbestpossible; }
	const Weight& getCC() const { return currentbestcertain; }
	void setEmptySetValue(const Weight& w) { emptysetvalue = w; }
	void setCP(const Weight& w) { currentbestpossible = w; }
	void setCC(const Weight& w) { currentbestcertain = w; }

	lwagg::const_iterator 	getAggBegin() 	const 	{ return aggregates.begin(); }
	lwagg::const_iterator 	getAggEnd() 	const 	{ return aggregates.end(); }
	void 					addAgg(weak_ptr<Agg> aggr)		{ aggregates.push_back(aggr); }
	int 					nbAgg() 				{ return aggregates.size(); }

	lwlv::const_iterator getWLBegin() 			const { return wlits.begin(); }
	lwlv::const_iterator getWLEnd()				const { return wlits.end(); }
	lwlv::const_reverse_iterator getWLRBegin() 	const { return wlits.rbegin(); }
	lwlv::const_reverse_iterator getWLREnd() 	const { return wlits.rend(); }
	const WLV& operator[](int i) 				const { return wlits[i]; }
	int size() const { return wlits.size(); }

	int getStackSize() const { return stack.size(); }
	const PropagationInfo getStackBack() const { return stack.back(); }
	lprop::const_iterator getStackBegin() 			const { return stack.begin(); }
	lprop::const_iterator getStackEnd()				const { return stack.end(); }
};

class AggrMaxSet: public AggrSet{
public:
	AggrMaxSet(vec<Lit>& lits, vector<Weight>& weights):AggrSet(lits, weights){
		name = "MAX";
	};

	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) const;
	virtual WLit 	handleOccurenceOfBothSigns(const WLit& one, const WLit& two);

	virtual Weight 	getBestPossible			() 		const;
	virtual void 	initEmptySetValue		();
	virtual void 	addToCertainSet			(const WLit& l);
	virtual void 	removeFromPossibleSet	(const WLit& l);
};

class AggrSumSet: public AggrSet{
public:
	AggrSumSet(vec<Lit>& lits, vector<Weight>& weights):AggrSet(lits, weights){
		name = "SUM";
	};

	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) const;
	virtual WLit 	handleOccurenceOfBothSigns(const WLit& one, const WLit& two);

	virtual Weight 	getBestPossible			() 		const;
	virtual void 	initEmptySetValue		();
	virtual void 	addToCertainSet			(const WLit& l);
	virtual void 	removeFromPossibleSet	(const WLit& l);
};

class AggrProdSet: public AggrSet{
public:
	AggrProdSet(vec<Lit>& lits, vector<Weight>& weights):AggrSet(lits, weights){
		name = "PROD";
	};

	virtual Weight 	getCombinedWeight(const Weight& one, const Weight& two) const;
	virtual WLit 	handleOccurenceOfBothSigns(const WLit& one, const WLit& two);

	virtual Weight 	getBestPossible			() 		const;
	virtual void 	initEmptySetValue		();
	virtual void 	addToCertainSet			(const WLit& l);
	virtual void 	removeFromPossibleSet	(const WLit& l);
};

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

	AggrSet* 	set;

public:

    Agg(bool lower, Weight bound, Lit head, AggrSet* set) :
	    bound(bound), lower(lower), head(head), headindex(-1), headvalue(l_Undef), set(set) {
    	//FIXME FIXME
    	//set->addAgg(this);
    }

    /**
     * GET-SET METHODS
     */
    const 	Weight& getBound()		const	{ return bound; }
			bool 	isLower()		const	{ return lower; }
	const 	Lit& 	getHead()		const	{ return head; }
	const 	lbool& 	getHeadValue() 	const	{ return headvalue; }
			int 	getHeadIndex() 	const	{ return headindex; }
	const 	AggrSet*	getSet() 	const	{ return set; }

	void 	setBound(const Weight& b)	{ bound = b; }

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

    virtual shared_ptr<Agg> getAgg()
    {
        return shared_from_this();
    }
};

class MaxAgg: public Agg {
public:
	MaxAgg(bool lower, Weight bound, Lit head, AggrMaxSet* set):
		Agg(lower, bound, head, set){
	};

    virtual Clause* propagate		(bool headtrue);
    virtual Clause* propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPAgg: public Agg {
private:
	bool sum;

public:
	SPAgg(bool lower, Weight bound, Lit head, AggrSet* set, bool sum):
		Agg(lower, bound, head, set),sum(sum){
	};

    virtual Clause* propagate		(bool headtrue);
    virtual Clause* propagateHead	(bool headtrue);

	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) const;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SumAgg: public SPAgg {
public:
	SumAgg(bool lower, Weight bound, Lit head, AggrSumSet* set):
		SPAgg(lower, bound, head, set, true){
	};

	void	getMinimExplan(vec<Lit>& lits);
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(bool lower, Weight bound, Lit head, AggrProdSet* set):
		SPAgg(lower, bound, head, set, false){
	}
};

#endif /* MINAGG_H_ */
