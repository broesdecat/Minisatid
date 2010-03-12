#ifndef MINAGG_H_
#define MINAGG_H_

#include <limits>
#include <vector>
#include <set>
#include <iostream>

#include "Vec.h"
#include "SolverTypes.h"

using namespace std;

class Agg;
class MaxAgg;
class ProdAgg;
class SumAgg;
class AggrSet;

struct WLV;
struct PropagationInfo;

typedef vector<WLV> lwlv;
typedef vector<Agg*> lagg;
typedef vector<PropagationInfo> lprop;

enum AggrType {SUM, PROD, MIN, MAX};
enum Occurrence {HEAD, POS, NEG};

struct WLit {  // Weighted literal
public:
	Lit	lit;
	Weight	weight;

    WLit(Lit l, Weight w) : lit(l), weight(w) {}

    bool operator<	(const WLit& p)		 const { return weight < p.weight; }
    bool operator<	(const Weight& bound)const { return weight < bound; }
    bool operator==	(const WLit& p)		 const { return weight == p.weight && lit==p.lit; }
};

struct WLV: public WLit{
public:
	lbool value;

	WLV(Lit l, Weight w, lbool value) : WLit(l, w), value(value) {}
};

struct PropagationInfo {	// Propagated literal
	WLit        wlit;		// value(lit)==l_True.
    Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagate)
    Weight prevbestcertain, prevbestpossible; //values BEFORE the propagation was added

    PropagationInfo(Lit l, Weight w, Occurrence t, Weight prevcertain, Weight prevpossible) : wlit(WLit(l,w)), type(t), prevbestcertain(prevcertain), prevbestpossible(prevpossible) {}
};

struct AggrWatch {
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    AggrSet*	set;
    int			index;

    AggrWatch(AggrSet* e, int i, Occurrence t) : type(t), set(e), index(i) {}
};

struct AggrReason {
    Agg*		expr;
    int 		index;

    AggrReason(Agg* e, int index) : expr(e), index(index) {}
};

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
class AggrSet {
public:
	lagg	aggregates;
	lwlv 	wlits;

    Weight currentbestcertain, currentbestpossible, emptysetvalue;
			//current keeps the currently derived min and max bounds
			//truecount is the number of literals certainly in the set

    lprop stack;		// Stack of propagations of this expression so far.

    string name;

    AggrSet(vec<Lit>& lits, vector<Weight>& weights):currentbestcertain(0),currentbestpossible(0),emptysetvalue(0){
    	for (int i = 0; i < lits.size(); i++) {
			wlits.push_back(WLV(lits[i], weights[i], l_Undef));
		}
		sort(wlits.begin(), wlits.end());
    };

			void initialize();
			Clause* propagate		(Lit p, AggrWatch& ws);
    virtual void 	backtrack		(int index);

    virtual Clause* propagateBodies();

	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 * @post: each literal only occurs once in the set.
	 * @remark: has to be called in the SUBCLASS constructors, because it needs the subclass data of which agg it is.
	 */
			void 	doSetReduction();
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual Weight 	getCombinedWeight(Weight one, Weight two) = 0;
	virtual WLit 	handleOccurenceOfBothSigns(WLit one, WLit two) = 0;

	virtual Weight 	getBestPossible			() 		 = 0;
	virtual void 	initEmptySetValue		()		 = 0;
	virtual void 	addToCertainSet			(WLit l) = 0;
	virtual void 	removeFromPossibleSet	(WLit l) = 0;

	bool isJustified		(Var x, vec<int>& currentjust);
	bool isJustified		(WLV& elem, vec<int>& currentjust, bool real);
	bool oppositeIsJustified(WLV& elem, vec<int>& currentjust, bool real);
};

class AggrMaxSet: public AggrSet{
public:
	AggrMaxSet(vec<Lit>& lits, vector<Weight>& weights):AggrSet(lits, weights){
		emptysetvalue = Weight(0);
		name = "MAX";
	};

	virtual Weight 	getCombinedWeight(Weight one, Weight two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual Weight 	getBestPossible			();
	virtual void 	initEmptySetValue		();
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	removeFromPossibleSet	(WLit l);
};

class AggrSumSet: public AggrSet{
public:
	AggrSumSet(vec<Lit>& lits, vector<Weight>& weights):AggrSet(lits, weights){
		emptysetvalue = Weight(0);
		name = "SUM";
	};

	virtual Weight 	getCombinedWeight(Weight one, Weight two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual Weight 	getBestPossible			();
	virtual void 	initEmptySetValue		();
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	removeFromPossibleSet	(WLit l);
};

class AggrProdSet: public AggrSet{
public:
	AggrProdSet(vec<Lit>& lits, vector<Weight>& weights):AggrSet(lits, weights){
		emptysetvalue = Weight(1);
		name = "PROD";
	};

	virtual Weight 	getCombinedWeight(Weight one, Weight two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual Weight 	getBestPossible			();
	virtual void 	initEmptySetValue		();
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	removeFromPossibleSet	(WLit l);
};

/**
 * The certain values contain info about the elements of the set that are currently CERTAINLY in the set (by their
 * truth value).
 * The possible values contain info about all elements that eventually MIGHT still be in the set (by their truth value).
 *
 * An aggregate is (currently) always a definition, so its head is always a positive literal.
 */

class Agg{
public:
	Weight		bound;
	bool 		lower;

    Lit			head;
    int			headindex;	//the index in the stack when this was derived
    lbool		headvalue;

    AggrSet* 	set;

    Agg(bool lower, Weight bound, Lit head, AggrSet* set) :
	    bound(bound), lower(lower), head(head), headindex(-1), headvalue(l_Undef), set(set) {
    }

			void 	backtrackHead();
			Clause*	propagateHead(Lit p);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead() = 0;

    virtual Clause* propagate		(bool headtrue) = 0;
    virtual Clause* propagateHead	(bool headtrue) = 0;

    /**
     * Should find a set L+ such that "bigwedge{l | l in L+} implies p"
     * which is equivalent with the clause bigvee{~l|l in L+} or p
     * and this is returned as the set {~l|l in L+}
     */
    virtual void	getExplanation	(vec<Lit>& lits, AggrReason& ar) = 0;
	//virtual void	getExplanation	(Lit p, vec<Lit>& lits, AggrReason& ar) = 0;

			void 	becomesCycleSource(vec<Lit>& nj) const;
	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) = 0;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const = 0;
};

class MaxAgg: public Agg {
public:
	MaxAgg(bool lower, Weight bound, Lit head, AggrMaxSet* set):
		Agg(lower, bound, head, set){
		set->aggregates.push_back(this);
	};

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	//void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);
	void	getExplanation(vec<Lit>& lits, AggrReason& ar);

	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SPAgg: public Agg {
private:
	bool sum;
public:
	SPAgg(bool lower, Weight bound, Lit head, AggrSet* set, bool sum):
		Agg(lower, bound, head, set),sum(sum){
	};

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	//void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);
	void	getExplanation(vec<Lit>& lits, AggrReason& ar);

	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) const;
};

class SumAgg: public SPAgg {
public:
	SumAgg(bool lower, Weight bound, Lit head, AggrSumSet* set):
		SPAgg(lower, bound, head, set, true){
		set->aggregates.push_back(this);
	};

	void	getMinimExplan(vec<Lit>& lits);
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(bool lower, Weight bound, Lit head, AggrProdSet* set):
		SPAgg(lower, bound, head, set, false){
		set->aggregates.push_back(this);
	}
};

#endif /* MINAGG_H_ */
