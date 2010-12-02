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
	const 	WL&		wl;	//the literal as it occurs in the set
public:
	Watch(TypedSet* set, const WL& wl):
		set(set), wl(wl){}

	virtual ~Watch(){}

	TypedSet*		getSet		()	 		const 	{ return set; }
	//Return POS if the literal in the set was provided, otherwise neg
	Occurrence 		getType		(const Lit& p)	const 	{ return p==wl.getLit()?POS:NEG; }

	virtual const WL&	getWL	()			const	{ return wl; }
};

enum Expl{BASEDONCC,BASEDONCP,HEADONLY,BASEDONBOTH};

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
