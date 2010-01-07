#ifndef MINAGG_H_
#define MINAGG_H_

#include <limits>
#include "Vec.h"
#include <vector>
#include "SolverTypes.h"

#include <iostream>

using namespace std;

class Agg;

typedef char AggrType;
const AggrType SUM  = 0; // NOTE: CARD = (SUM with weights =1).
const AggrType PROD = 1;
const AggrType MIN  = 2;
const AggrType MAX  = 3;
const int NB_AGGR_TYPES = 4;

typedef char Occurrence;
const Occurrence HEAD = 0;
const Occurrence POS  = 1;
const Occurrence NEG  = 2;

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

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
struct AggrSet {
    vector<WLit>	wlitset;	// Stores the actual set of weighted literals.

    AggrSet(){};
};

struct AggrWatch {
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    Agg*		expr;		// Not used (NULL) if type!=DEFN
    int			index;		// Not used if type==DEFN

    AggrWatch(Agg* e, int i, Occurrence t) : type(t), expr(e), index(i) {}
};
struct AggrReason {			// Needed to build (with implicitReasonClause(Lit)) a reason clause for a cardinality propagation.
    Agg&		expr;
    Occurrence	type;

    AggrReason(Agg& e, Occurrence t) : expr(e), type(t) {}
};

class Agg{
public:
	int	bound, currentbestcertain, currentbestpossible, emptysetValue, truecount, possiblecount;
					//current keeps the currently derived min and max bounds
					//truecount is the number of literals certainly in the set
	bool 		lower;
    string 		name;
    Lit			head;
    AggrSet& 	set;
    vec<lbool>	setcopy;			//same indices as set.wlitset. The value of the literal as how it has been propagated IN THIS EXPRESSIOn
    lbool		headvalue;			//same for head
    vec<PropagationInfo> stack;		// Stack of propagations of this expression so far.

    Agg(bool lower, int bound, Lit head, AggrSet& set) :
	    	bound(bound), emptysetValue(0), truecount(0), lower(lower), head(head), set(set) {
    }

    virtual void 	initialize();

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead();
    virtual Clause* propagate(bool headtrue) = 0;
    Clause* propagate(Lit p, AggrWatch& ws);
    virtual void 	backtrack(Occurrence tp, int index);
	virtual void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar) = 0;

	virtual int getBestPossible() = 0;
	virtual void removeFromCertainSet(WLit l) = 0;
	virtual void addToCertainSet(WLit l) = 0;
	virtual void addToPossibleSet(WLit l) = 0;
	virtual void removeFromPossibleSet(WLit l) = 0;

	//cannot be done in the agg constructor, because it needs a subclass OBJECT to work with, which is only constructed later
	virtual void doSetReduction();

	virtual void replaceEmptysetValue(int value) = 0;
	virtual bool isBetter(int one, int two) = 0;
	virtual int	 getCombinedWeightFirstBetter(int, int) = 0;
};

class MinAgg: public Agg {
public:
	MinAgg(bool lower, int bound, Lit head, AggrSet& set):
		Agg(lower, bound, head, set){
			emptysetValue = std::numeric_limits<int>::max();
			name = "MIN";
			doSetReduction();
			setcopy.growTo(set.wlitset.size(), l_Undef);
		};

	virtual ~MinAgg();

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar);

	int 	getBestPossible();
	void	removeFromCertainSet(WLit l);
	void	addToCertainSet(WLit l);
	void	addToPossibleSet(WLit l);
	void	removeFromPossibleSet(WLit l);

	void replaceEmptysetValue(int value);
	bool isBetter(int one, int two);
	int	 getCombinedWeightFirstBetter(int, int);
};

class MaxAgg: public Agg {
public:
	MaxAgg(bool lower, int bound, Lit head, AggrSet& set):
		Agg(lower, bound, head, set){
			emptysetValue = std::numeric_limits<int>::min();
			name = "MAX";
			doSetReduction();
			setcopy.growTo(set.wlitset.size(), l_Undef);
		};

	virtual ~MaxAgg();

	Clause* propagate(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar);

	int 	getBestPossible();
	void	removeFromCertainSet(WLit l);
	void	addToCertainSet(WLit l);
	void	addToPossibleSet(WLit l);
	void	removeFromPossibleSet(WLit l);

	void replaceEmptysetValue(int value);
	bool isBetter(int one, int two);
	int	 getCombinedWeightFirstBetter(int, int);
};

class SPAgg: public Agg {
private:
	bool sum;
public:
	SPAgg(bool lower, int bound, Lit head, AggrSet& set, bool sum):
		Agg(lower, bound, head, set),sum(sum){
			if(sum){
				emptysetValue = 0;
				name = "SUM";
			}else{
				emptysetValue = 1;
				name = "PROD";
			}
			doSetReduction();
			setcopy.growTo(set.wlitset.size(), l_Undef);
		};
	virtual ~SPAgg();

	Clause* propagate(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar);

	int 	getBestPossible();
	void	removeFromCertainSet(WLit l);
	void	addToCertainSet(WLit l);
	void	addToPossibleSet(WLit l);
	void	removeFromPossibleSet(WLit l);

	void replaceEmptysetValue(int value);
	bool isBetter(int one, int two);
	int	 getCombinedWeightFirstBetter(int, int);
};

#endif /* MINAGG_H_ */
