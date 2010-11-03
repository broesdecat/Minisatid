/*
 * AggComb.hpp
 *
 *  Created on: Aug 26, 2010
 *      Author: broes
 */

#ifndef AGGCOMB_HPP_
#define AGGCOMB_HPP_

#include "solvers/utils/Utils.hpp"
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
};


class Watch{
private:
			TypedSet* 	set;
			int 	index;
	const 	bool 	setlit;	//true if set literal, false if agg head
	const 	bool 	pos; 	//true if the literal occurs in the set, false if its negation is in the set
public:
	Watch(TypedSet* set, int index, bool setlit, bool pos):
		set(set), index(index), setlit(setlit), pos(pos){}

	virtual 	~Watch(){}

	TypedSet*	getSet()	 	const { return set; }
	int 		getIndex() 		const { return index; }
	void		setIndex(int i) 	  { index = i; }
	bool 		isSetLit() 		const { return setlit; }
	bool		isPos()			const { return pos; }
	Occurrence 	getType()		const { return !set?HEAD:pos?POS:NEG; }

	virtual const WL&	getWL()			const; //TODO unclear semantics
};

enum Expl{BASEDONCC,BASEDONCP,CPANDCC, HEADONLY};

class AggReason {
private:
	const Agg&	expr;
	const Lit	l, proplit; //l is the literal which caused the propagation of proplit, if toInt(l)<0, then there is no cause!
	const Expl	expl;
	const bool 	head;
	vec<Lit> 	explanation;
	bool 		hasclause;

public:
	AggReason(const Agg& agg, const Lit& l, Expl expl, const Lit& proplit, bool head = false)
		:expr(agg), l(l), proplit(proplit), expl(expl), head(head), explanation(), hasclause(false){
	}

	const Agg&	getAgg() 		const	{ return expr; }
    const Lit&	getLit() 		const	{ return l; }
    const Lit&	getPropLit()	const	{ return proplit; }
    bool		isHeadReason() 	const	{ return head; }
    Expl		getExpl() 		const	{ return expl; }

    bool 		hasClause() 	const { return hasclause; }
    const vec<Lit>&	getClause() const { return explanation; }
    void		setClause(const Minisat::vec<Lit>& c) {	c.copyTo(explanation); hasclause = true; }
};

void printAgg(const TypedSet&, bool printendline = false);
void printAgg(const Agg& c, bool printendline = false);

///////
// ID support
///////
bool 	oppositeIsJustified		(const WL& wl, vec<int>& currentjust, bool real, AggSolver const * const solver);
bool 	isJustified				(const WL& wl, vec<int>& currentjust, bool real, AggSolver const * const solver);
bool 	isJustified				(Var x, vec<int>& currentjust);

}
}

#endif /* AGGCOMB_HPP_ */
