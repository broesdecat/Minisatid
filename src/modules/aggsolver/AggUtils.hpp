/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGGCOMB_HPP_
#define AGGCOMB_HPP_

#include "utils/Utils.hpp"
#include <vector>

namespace MinisatID{

class WL;
typedef std::vector<WL> vwl;
class AggSolver;


//FROM ID SOLVER
typedef std::vector<int> VarToJustif;

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
	//FIXME make this propagator instead of typedSet
private:
	TypedSet* 		set;
	const 	WL		wl;	//the literal as it occurs in the set
public:
	Watch(TypedSet* set, const WL& wl):
		set(set), wl(wl){}

	virtual ~Watch(){}

	TypedSet*		getSet		()	 		const 	{ return set; }
	//Return POS if the literal in the set was provided, otherwise neg
	Occurrence 		getType		(const Lit& p)	const 	{ return p==wl.getLit()?POS:NEG; }

	virtual const WL&	getWL	()			const	{ return wl; }
};

enum Expl{BASEDONCC,BASEDONCP,HEADONLY};

class AggReason {
private:
	const Expl	expl;
	vec<Lit> 	explanation;
	bool 		hasclause;

public:
	AggReason(Expl expl) :expl(expl), explanation(), hasclause(false){ }
	virtual ~AggReason() {}

	virtual const Agg&	getAgg			() 	const = 0;
	virtual Lit			getPropLit		()	const = 0;
	virtual Weight		getPropWeight	()	const = 0;
	virtual bool		isHeadReason	() 	const = 0;
	virtual bool		isInSet			()	const = 0;

	Expl		getExpl			()	const { return expl; }

    bool 		hasClause		()	const	{ return hasclause; }
    const vec<Lit>&	getClause	()	const	{ assert(hasClause()); return explanation; }
    void		setClause		(const Minisat::vec<Lit>& c) {	c.copyTo(explanation); hasclause = true; }
};

class HeadReason: public AggReason {
private:
	const Agg&	expr;
	const Lit 	proplit;

public:
	HeadReason(const Agg& agg, Expl expl, const Lit& proplit)
		:AggReason(expl), expr(agg), proplit(proplit){
	}

	const Agg&		getAgg			() 	const	{ return expr; }
    Lit				getPropLit		()	const	{ return proplit; }
    Weight			getPropWeight	()	const	{ assert(false); return Weight(-1); }
    bool			isHeadReason	() 	const	{ return true; }
    bool			isInSet			()	const	{ assert(false); return false; }
};

class SetLitReason: public AggReason{
private:
	const Agg&	expr;
	const Lit l;
	const Weight w;
	bool inset;

public:
	SetLitReason(const Agg& agg, const Lit& setlit, const Weight& setweight, Expl expl, bool inset)
		: AggReason(expl), expr(agg), l(setlit), w(setweight), inset(inset){ }

	const Agg&		getAgg			() 	const	{ return expr; }
    Lit				getPropLit		()	const	{ return inset?l:~l; }
    Weight			getPropWeight	()	const	{ return w; }
    bool			isHeadReason	() 	const	{ return false; }
    bool			isInSet			()	const	{ return inset; }
};

///////
// ID support
///////
bool 	oppositeIsJustified		(const WL& wl, VarToJustif& currentjust, bool real, AggSolver const * const solver);
bool 	isJustified				(const WL& wl, VarToJustif& currentjust, bool real, AggSolver const * const solver);
bool 	isJustified				(Var x, VarToJustif& currentjust);

}
}

#endif /* AGGCOMB_HPP_ */
