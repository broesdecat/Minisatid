#ifndef MINAGG_H_
#define MINAGG_H_

#include <limits>
#include "Vec.h"
#include "Queue.h"
#include <vector>
#include <set>
#include "SolverTypes.h"

#include <iostream>

using namespace std;

class Agg;
class MinAgg;
class MaxAgg;
class ProdAgg;
class SumAgg;
class AggrSet;

enum AggrType {SUM, PROD, MIN, MAX};
enum Occurrence {HEAD, POS, NEG};

inline Occurrence relativeOccurrence(Occurrence o, Lit l) {
    if (o==HEAD) return HEAD;
    if (o==POS)  return sign(l)? NEG : POS;
    else         return sign(l)? POS : NEG;
}

struct WLit {  // Weighted literal
	Lit	lit;
	int	weight;

    WLit(Lit l, int w) : lit(l), weight(w) {}

    bool operator <  (WLit p) const { return weight < p.weight; }
    bool operator <  (int bound) const { return weight < bound; }
    bool operator ==  (WLit p) const { return weight == p.weight && lit==p.lit; }
};

struct PropagationInfo {	// Propagated literal
	WLit        wlit;		// value(lit)==l_True.
    Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagate)

    PropagationInfo(Lit l, int w, Occurrence t) : wlit(WLit(l,w)), type(t) {}
};

struct AggrWatch {
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    AggrSet*	set;
    int			index;

    AggrWatch(AggrSet* e, int i, Occurrence t) : type(t), set(e), index(i) {}
};

struct AggrReason {
    Agg*		expr;
    Occurrence	type;
    int 		index; //the index of the literal, in the weight set of expr, for which this is the reason (-1 if head)

    AggrReason(Agg* e, Occurrence t, int index) : expr(e), type(t), index(index) {}
};

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
class AggrSet {
public:
	vector<Agg*>	aggregates;
    vector<WLit>	wlitset;	// Stores the actual set of weighted literals.
    int 			currentbestcertain, currentbestpossible, truecount, possiblecount;
						//current keeps the currently derived min and max bounds
						//truecount is the number of literals certainly in the set
    int 			emptysetValue;

    vec<lbool>		litvalue;			//same indices as set.wlitset. The value of the literal as how it has been propagated IN THIS EXPRESSIOn
    vec<PropagationInfo> stack;		// Stack of propagations of this expression so far.

    string 			name;

    AggrSet(vec<Lit>& lits, vec<int>& weights){
		for (int i = 0; i < lits.size(); i++) {
			wlitset.push_back(WLit(lits[i], weights[i]));
		}
		sort(wlitset.begin(), wlitset.end());
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
	virtual int	 	getCombinedWeight(int one, int two) = 0;
	virtual WLit 	handleOccurenceOfBothSigns(WLit one, WLit two) = 0;

	virtual int 	getBestPossible			() 		 = 0;
    /*virtual void 	addToSet				(WLit l) = 0;
    virtual void 	removeFromSet			(WLit l) = 0;*/
	virtual void 	removeFromCertainSet	(WLit l) = 0;
	virtual void 	addToCertainSet			(WLit l) = 0;
	virtual void 	addToPossibleSet		(WLit l) = 0;
	virtual void 	removeFromPossibleSet	(WLit l) = 0;

	bool isJustified		(Var x, vec<int>& currentjust);
	bool isJustified		(int index, vec<int>& currentjust, bool real);
	bool oppositeIsJustified(int index, vec<int>& currentjust, bool real);
};

class AggrMinSet: public AggrSet{
public:
	AggrMinSet(vec<Lit>& lits, vec<int>& weights):AggrSet(lits, weights){
		emptysetValue = std::numeric_limits<int>::max();
		name = "MIN";
		doSetReduction();
		litvalue.growTo(wlitset.size(), l_Undef); //only initialize after setreduction!
	};

	virtual int	 	getCombinedWeight			(int one, int two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual int 	getBestPossible			();
    /*virtual void 	addToSet				(WLit l);
    virtual void 	removeFromSet			(WLit l);*/
	virtual void 	removeFromCertainSet	(WLit l);
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	addToPossibleSet		(WLit l);
	virtual void 	removeFromPossibleSet	(WLit l);
};

class AggrMaxSet: public AggrSet{
public:
	AggrMaxSet(vec<Lit>& lits, vec<int>& weights):AggrSet(lits, weights){
		emptysetValue = std::numeric_limits<int>::min();
		name = "MAX";
		doSetReduction();
		litvalue.growTo(wlitset.size(), l_Undef); //only initialize after setreduction!
	};

	virtual int	 	getCombinedWeight			(int one, int two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual int 	getBestPossible			();
    /*virtual void 	addToSet				(WLit l);
    virtual void 	removeFromSet			(WLit l);*/
	virtual void 	removeFromCertainSet	(WLit l);
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	addToPossibleSet		(WLit l);
	virtual void 	removeFromPossibleSet	(WLit l);
};

class AggrSumSet: public AggrSet{
public:
	AggrSumSet(vec<Lit>& lits, vec<int>& weights):AggrSet(lits, weights){
		emptysetValue = 0;
		name = "SUM";
		doSetReduction();
		litvalue.growTo(wlitset.size(), l_Undef); //only initialize after setreduction!
	};

	virtual int	 	getCombinedWeight			(int one, int two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual int 	getBestPossible			();
    /*virtual void 	addToSet				(WLit l);
    virtual void 	removeFromSet			(WLit l);*/
	virtual void 	removeFromCertainSet	(WLit l);
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	addToPossibleSet		(WLit l);
	virtual void 	removeFromPossibleSet	(WLit l);
};

class AggrProdSet: public AggrSet{
public:
	AggrProdSet(vec<Lit>& lits, vec<int>& weights):AggrSet(lits, weights){
		emptysetValue = 1;
		name = "PROD";
		doSetReduction();
		litvalue.growTo(wlitset.size(), l_Undef); //only initialize after setreduction!
	};

	virtual int	 	getCombinedWeight			(int one, int two);
	virtual WLit 	handleOccurenceOfBothSigns	(WLit one, WLit two);

	virtual int 	getBestPossible			();
    /*virtual void 	addToSet				(WLit l);
    virtual void 	removeFromSet			(WLit l);*/
	virtual void 	removeFromCertainSet	(WLit l);
	virtual void 	addToCertainSet			(WLit l);
	virtual void 	addToPossibleSet		(WLit l);
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
	int			bound;
	bool 		lower;

    Lit			head;
    lbool		headvalue;
    int			headindex;	//the index in the stack when this was derived

    AggrSet* 	set;

    Agg(bool lower, int bound, Lit head, AggrSet* set) :
	    bound(bound), lower(lower), head(head), set(set), headindex(-1) {
    }

			void 	backtrackHead();
			Clause*	propagateHead(Lit p);

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead() = 0;

    virtual Clause* propagate		(bool headtrue) = 0;
    virtual Clause* propagateHead	(bool headtrue) = 0;
	virtual void	getExplanation	(Lit p, vec<Lit>& lits, AggrReason& ar) = 0;

			void 	becomesCycleSource(vec<Lit>& nj);
	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) = 0;
	virtual bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real) = 0;
};

class MinAgg: public Agg {
public:
	MinAgg(bool lower, int bound, Lit head, AggrMinSet* set):
		Agg(lower, bound, head, set){
		set->aggregates.push_back(this);
	};

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);

	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real);
};

class MaxAgg: public Agg {
public:
	MaxAgg(bool lower, int bound, Lit head, AggrMaxSet* set):
		Agg(lower, bound, head, set){
		set->aggregates.push_back(this);
	};

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);

	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real);
};

class SPAgg: public Agg {
private:
	bool sum;
public:
	SPAgg(bool lower, int bound, Lit head, AggrSet* set, bool sum):
		Agg(lower, bound, head, set),sum(sum){
	};

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);

	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool 	canJustifyHead(vec<Lit>& jstf, vec<Var>& nonjstf, vec<int>& currentjust, bool real);
};

class SumAgg: public SPAgg {
public:
	SumAgg(bool lower, int bound, Lit head, AggrSumSet* set):
		SPAgg(lower, bound, head, set, true){
		set->aggregates.push_back(this);
	};
};

class ProdAgg: public SPAgg {
public:
	ProdAgg(bool lower, int bound, Lit head, AggrProdSet* set):
		SPAgg(lower, bound, head, set, false){
		set->aggregates.push_back(this);
	}
};

#endif /* MINAGG_H_ */
