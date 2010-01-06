#ifndef MINAGG_H_
#define MINAGG_H_

#include <limits>
#include "Vec.h"
#include "SolverTypes.h"

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
};

struct PropagationInfo {	// Propagated literal
	WLit        wlit;		// value(lit)==l_True.
    Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagate)

    PropagationInfo(Lit l, int w, Occurrence t) : wlit(WLit(l,w)), type(t) {}
};

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
struct AggrSet {
    vec<WLit>	wlitset;	// Stores the actual set of weighted literals.
    vec<Agg*>	exprs;		// In which expressions does this set occur. NOTE: there's no point in splitting this in "already satisfied" and "not yet satisfied"; we can't avoid doing most of the propagation work anew.

    AggrSet(){};
};

struct AggrWatch {
    Occurrence	type;
    Agg*		expr;		// Not used (NULL) if type!=DEFN
    int			index;		// Not used if type==DEFN

    AggrWatch(Agg* e, int i, Occurrence t) : type(t), expr(e), index(i) {}
};
struct AggrReason {			// Needed to build (with implicitReasonClause(Lit)) a reason clause for a cardinality propagation.
    Agg&		expr;
    Occurrence	type;

    AggrReason(Agg& e, Occurrence t) : expr(e), type(t) {}
};

inline int compare_WLits(const void* a, const void* b) {
    WLit* arg1 = (WLit*)a;
    WLit* arg2 = (WLit*)b;
    if (arg1->weight < arg2->weight) return -1;
    else if (arg1->weight == arg2->weight) return 0;
    else return 1;
}

class Agg{
public:
	int	bound, currentworst, currentbest, emptysetValue, truecount; //current keeps the currently derived min and max bounds
	//truecount is the number of literals certainly in the set
	bool 		lower;
    Lit			head;
    AggrSet& 	set;
    vec<PropagationInfo> stack;		// Stack of propagations of this expression so far.

    Agg(bool lower, int bound, Lit head, AggrSet& set) :
	    	bound(bound), emptysetValue(0), truecount(0), lower(lower), head(head), set(set) {}

    virtual void 	initialize();

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	updateAndCheckPropagate(WLit l, bool addtoset);
    virtual Clause* propagate(bool headtrue) = 0;
    virtual void 	backtrack(WLit l, bool wasinset);
	virtual void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar) = 0;

    virtual int 	getCurrentBestPossible(bool alltimebest=false) = 0;
    virtual int 	getCurrentBestCertain() = 0;

			lbool	value(Lit p);

			void	printAgg(const char* name) const;
    virtual void 	print() const = 0;
};

class MIMAAgg: public Agg {
private:
	bool min;
public:
	MIMAAgg(bool lower, int bound, Lit head, AggrSet& set, bool min):
		Agg(lower, bound, head, set), min(min){
			if(min){
				emptysetValue = std::numeric_limits<int>::max();
			}else{
				emptysetValue = std::numeric_limits<int>::min();
			}
		};

	virtual ~MIMAAgg();

	lbool 	updateAndCheckPropagate(WLit l, bool addtoset);
	Clause* propagate(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar);

	int 	getCurrentBestPossible(bool alltimebest=false);
	int 	getCurrentBestCertain();

	void 	print() const;
};

class SPAgg: public Agg {
private:
	bool sum;
public:
	SPAgg(bool lower, int bound, Lit head, AggrSet& set, bool sum):
		Agg(lower, bound, head, set),sum(sum){
			if(sum){
				emptysetValue = 0;
			}else{
				emptysetValue = 1;
			}

		};
	virtual ~SPAgg();

	Clause* propagate(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, int p_index, AggrReason& ar);

	int 	getCurrentBestPossible(bool alltimebest=false);
	int 	getCurrentBestCertain();

	void 	print() const;
};

#endif /* MINAGG_H_ */
