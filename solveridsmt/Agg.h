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

//INVARIANT: the WLITset is stored sorted from smallest to largest weight!
struct AggrSet {
    vector<WLit>	wlitset;	// Stores the actual set of weighted literals.

    AggrSet(){};
};

struct AggrWatch {
    Occurrence	type;		//whether the watch is on the head(HEAD), on the literal in the set(POS) or on its negation(NEG)
    Agg*		expr;		// Not used (NULL) if type!=HEAD
    int			index;		// Not used if type==HEAD

    AggrWatch(Agg* e, int i, Occurrence t) : type(t), expr(e), index(i) {}
};
struct AggrReason {
    Agg*		expr;
    Occurrence	type;
    int 		index; //the index of the literal, in the weight set of expr, for which this is the reason (-1 if head)

    AggrReason(Agg* e, Occurrence t, int index) : expr(e), type(t), index(index) {}
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
	int	bound, currentbestcertain, currentbestpossible, emptysetValue, truecount, possiblecount;
					//current keeps the currently derived min and max bounds
					//truecount is the number of literals certainly in the set
	bool 		lower;
    string 		name;
    Lit			head;
    AggrSet* 	set;
    vec<lbool>	litvalue;			//same indices as set.wlitset. The value of the literal as how it has been propagated IN THIS EXPRESSIOn
    lbool		headvalue;			//same for head
    vec<PropagationInfo> stack;		// Stack of propagations of this expression so far.

    Agg(bool lower, int bound, Lit head, AggrSet* set) :
	    	bound(bound), emptysetValue(0), truecount(0), lower(lower), head(head), set(set) {
    }

    virtual void 	initialize();

    /**
     * Updates the values of the aggregate and then returns whether the head can be directly propagated from the body
     */
    virtual lbool 	canPropagateHead() = 0;
			Clause* propagate		(Lit p, AggrWatch& ws);
    virtual void 	backtrack		(Occurrence tp, int index);

    virtual Clause* propagate		(bool headtrue) = 0;
    virtual Clause* propagateHead	(bool headtrue) = 0;
	virtual void	getExplanation	(Lit p, vec<Lit>& lits, AggrReason& ar) = 0;

	/**
	 * Checks whether duplicate literals occur in the set. If this is the case, their values are appropriately combined.
	 *
	 * @post: each literal only occurs once in the set.
	 *
	 * @remark: has to be called in the SUBCLASS constructors, because it needs the subclass data of which agg it is.
	 */
			void 	doSetReduction();
	//Returns the weight a combined literal should have if both weights are in the set at the same time
	virtual int	 	getCombinedWeight(int one, int two) = 0;
	virtual WLit 	handleOccurenceOfBothSigns(WLit one, WLit two) = 0;

	virtual void	propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify) = 0;
			void 	becomesCycleSource(vec<Lit>& nj);
	virtual void 	justifyHead(vec<Lit>& just) = 0;
	virtual void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) = 0;
	virtual bool	directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc) = 0;

	virtual int 	getBestPossible			() 		 = 0;
	virtual void 	removeFromCertainSet	(WLit l) = 0;
	virtual void 	addToCertainSet			(WLit l) = 0;
	virtual void 	addToPossibleSet		(WLit l) = 0;
	virtual void 	removeFromPossibleSet	(WLit l) = 0;
};

class MinAgg: public Agg {
public:
	MinAgg(bool lower, int bound, Lit head, AggrSet* set):
		Agg(lower, bound, head, set){
			emptysetValue = std::numeric_limits<int>::max();
			name = "MIN";
			doSetReduction();
			litvalue.growTo(set->wlitset.size(), l_Undef); //only initialize after setreduction!
		};

	virtual ~MinAgg();

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);

	int	 	getCombinedWeight(int, int);
	WLit 	handleOccurenceOfBothSigns(WLit one, WLit two);

	void	propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify);
	void 	justifyHead(vec<Lit>& just);
	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool	directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc);

	int 	getBestPossible();
	void	addToCertainSet			(WLit l);
	void	addToPossibleSet		(WLit l);
	void	removeFromCertainSet	(WLit l);
	void	removeFromPossibleSet	(WLit l);
};

class MaxAgg: public Agg {
public:
	MaxAgg(bool lower, int bound, Lit head, AggrSet* set):
		Agg(lower, bound, head, set){
			emptysetValue = std::numeric_limits<int>::min();
			name = "MAX";
			doSetReduction();
			litvalue.growTo(set->wlitset.size(), l_Undef); //only initialize after setreduction!
		};

	virtual ~MaxAgg();

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);

	int	 	getCombinedWeight(int, int);
	WLit 	handleOccurenceOfBothSigns(WLit one, WLit two);

	void	propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify);
	void 	justifyHead(vec<Lit>& just);
	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool	directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc);

	int 	getBestPossible();
	void	addToCertainSet			(WLit l);
	void	addToPossibleSet		(WLit l);
	void	removeFromCertainSet	(WLit l);
	void	removeFromPossibleSet	(WLit l);
};

class SPAgg: public Agg {
private:
	bool sum;
public:
	SPAgg(bool lower, int bound, Lit head, AggrSet* set, bool sum):
		Agg(lower, bound, head, set),sum(sum){
			if(sum){
				emptysetValue = 0;
				name = "SUM";
			}else{
				emptysetValue = 1;
				name = "PROD";
			}
			doSetReduction();
			litvalue.growTo(set->wlitset.size(), l_Undef); //only initialize after setreduction!
		};
	virtual ~SPAgg();

	lbool 	canPropagateHead();
	Clause* propagate(bool headtrue);
	Clause* propagateHead(bool headtrue);
	void	getExplanation(Lit p, vec<Lit>& lits, AggrReason& ar);

	int		getCombinedWeight(int, int);
	WLit 	handleOccurenceOfBothSigns(WLit one, WLit two);

	void	propagateJustifications(vec<Lit>& jstf, vec<int>& nb_body_lits_to_justify);
	void 	justifyHead(vec<Lit>& just);
	void	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);
	bool	directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc);

	int 	getBestPossible();
	void	addToCertainSet			(WLit l);
	void	addToPossibleSet		(WLit l);
	void	removeFromCertainSet	(WLit l);
	void	removeFromPossibleSet	(WLit l);
};

#endif /* MINAGG_H_ */
