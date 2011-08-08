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

class PCSolver;

//FROM ID SOLVER
typedef std::vector<int> VarToJustif;

class TypedSet;
class Agg;

enum Occurrence {HEAD, POS, NEG};

struct AggBound{
	Weight bound;
	AggSign sign;

	AggBound(AggSign sign, const Weight& b):bound(b), sign(sign){}
};

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
	bool 			head, origlit;
	Agg*			agg;
	Lit 			proplit;
	Weight 			weight;
public:
	Watch(TypedSet* set, const Lit& lit, Agg* agg):
		set(set), head(true), origlit(false), agg(agg), proplit(lit), weight(0){}
	Watch(TypedSet* set, const Lit& lit, const Weight& weight, bool origlit):
		set(set), head(false), origlit(origlit), agg(NULL), proplit(lit), weight(weight){}

	bool			headWatch	() 	const 	{ return head; }
	TypedSet*		getSet		()	const 	{ return set; }
	Occurrence 		getType		()	const 	{ return origlit?POS:NEG; }
		//Return POS if the literal in the set was provided, otherwise neg
	bool			isOrigLit	()	const	{ return origlit; }
	const Lit&		getPropLit	()	const	{ return proplit; }
	Lit				getOrigLit	()	const	{ return origlit?proplit:~proplit; }
	const Weight&	getWeight	()	const 	{ return weight; }
	int				getAggIndex	()	const;

	void			propagate	();
};

class AggReason {
private:
	vec<Lit> 	explanation;
	bool 		hasclause;

public:
	AggReason(): explanation(), hasclause(false){ }
	virtual ~AggReason() {}

	virtual const Agg&	getAgg			() 	const = 0;
	virtual Lit			getPropLit		()	const = 0;
	virtual Weight		getPropWeight	()	const = 0;
	virtual bool		isHeadReason	() 	const = 0;
	virtual bool		isInSet			()	const = 0;

    bool 		hasClause		()	const	{ return hasclause; }
    const vec<Lit>&	getClause	()	const	{ assert(hasClause()); return explanation; }
    void		setClause		(const Minisat::vec<Lit>& c) {	c.copyTo(explanation); hasclause = true; }
};

class HeadReason: public AggReason {
private:
	const Agg&	expr;
	const Lit 	proplit;

public:
	HeadReason(const Agg& agg, const Lit& proplit)
		:AggReason(), expr(agg), proplit(proplit){
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
	SetLitReason(const Agg& agg, const Lit& setlit, const Weight& setweight, bool inset)
		: AggReason(), expr(agg), l(setlit), w(setweight), inset(inset){ }

	const Agg&		getAgg			() 	const	{ return expr; }
    Lit				getPropLit		()	const	{ return inset?l:~l; }
    Weight			getPropWeight	()	const	{ return w; }
    bool			isHeadReason	() 	const	{ return false; }
    bool			isInSet			()	const	{ return inset; }
};

// ID support

bool 	oppositeIsJustified		(const WL& wl, VarToJustif& currentjust, bool real, PCSolver const * const solver);
bool 	isJustified				(const WL& wl, VarToJustif& currentjust, bool real, PCSolver const * const solver);
bool 	isJustified				(Var x, VarToJustif& currentjust);

}

#endif /* AGGCOMB_HPP_ */
