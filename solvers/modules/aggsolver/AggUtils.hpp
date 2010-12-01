#ifndef AGGCOMB_HPP_
#define AGGCOMB_HPP_

#include "utils/Utils.hpp"
#include <vector>

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;
class AggSolver;

namespace Aggrs{
class TypedSet;
class Agg;

enum Occurrence {HEAD, POS, NEG};

class PropagationInfo {	// Propagated literal
private:
	WL wl;
	Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagated)

public:
    PropagationInfo(const Lit& l, const Weight& w, Occurrence t) :
    	wl(l, w), type(t) {}

    const Lit& 			getLit()	const { return wl.getLit(); }
    const Weight&		getWeight()	const { return wl.getWeight(); }
    const Occurrence& 	getType() 	const { return type; }
    const WL& 			getWL()		const { return wl; }
};


class Watch{
private:
	TypedSet* 		set;
			int 	index;
	const 	bool 	setlit;	//true if set literal, false if agg head
	const 	bool 	pos; 	//if true, the positive literal is in the set, otherwise the negation
public:
	Watch(TypedSet* set, int index, bool setlit, bool pos):
		set(set), index(index), setlit(setlit), pos(pos){}

	virtual ~Watch(){}

	TypedSet*		getSet		()	 		const 	{ return set; }
	int 			getIndex	() 			const 	{ return index; }
	void			setIndex	(int i) 	  		{ index = i; }
	bool 			isSetLit	() 			const 	{ return setlit; }
	Occurrence 		getType		(bool neg)	const 	{ return !setlit?HEAD:((!neg && pos) || (neg && !pos))?POS:NEG; }

	virtual const WL&	getWL	()			const; //TODO unclear semantics
};

enum Expl{BASEDONCC,BASEDONCP,HEADONLY, BASEDONBOTH};

class AggReason {
private:
	const Agg&	expr;
	const Lit 	proplit;
	const Weight propweight;
	const Expl	expl;
	const bool 	head;
	vec<Lit> 	explanation;
	bool 		hasclause;

public:
	AggReason(const Agg& agg, Expl expl, const Lit& proplit, const Weight& propweight, bool head = false)
		:expr(agg), proplit(proplit), propweight(propweight), expl(expl), head(head), explanation(), hasclause(false){
	}

	const Agg&	getAgg			() 	const	{ return expr; }
    const Lit&	getPropLit		()	const	{ return proplit; }
    const Weight&	getPropWeight()	const	{ return propweight; }
    bool		isHeadReason	() 	const	{ return head; }
    Expl		getExpl			()	const	{ return expl; }

    bool 		hasClause		()	const	{ return hasclause; }
    const vec<Lit>&	getClause	()	const	{ return explanation; }
    void		setClause		(const Minisat::vec<Lit>& c) {	c.copyTo(explanation); hasclause = true; }
};

///////
// ID support
///////
bool 	oppositeIsJustified		(const WL& wl, vec<int>& currentjust, bool real, AggSolver const * const solver);
bool 	isJustified				(const WL& wl, vec<int>& currentjust, bool real, AggSolver const * const solver);
bool 	isJustified				(Var x, vec<int>& currentjust);

}
}

#endif /* AGGCOMB_HPP_ */
