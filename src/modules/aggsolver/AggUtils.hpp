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

typedef std::vector<WL> vwl;

class PCSolver;

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


class Watch: public GenWatch{
private:
	TypedSet* 		set_;
	bool 			head_, origlit_, dynamic_;
	Agg*			agg_;
	Lit 			proplit_;
	Weight 			weight_;
public:
	Watch(TypedSet* set, const Lit& lit, Agg* agg, bool dynamic):
			set_(set),
			head_(true), origlit_(false), dynamic_(dynamic),
			agg_(agg),
			proplit_(lit),
			weight_(0){}
	Watch(TypedSet* set, const Lit& lit, const Weight& weight, bool origlit, bool dynamic):
			set_(set),
			head_(false), origlit_(origlit), dynamic_(dynamic),
			agg_(NULL),
			proplit_(lit),
			weight_(weight){}

	virtual ~Watch(){}

	bool 			dynamic		() 	const	{ return dynamic_; }

	bool			headWatch	() 	const 	{ return head_; }
	TypedSet*		getSet		()	const 	{ return set_; }
	Occurrence 		getType		()	const 	{ return origlit_?POS:NEG; }
		//Return POS if the literal in the set was provided, otherwise neg
	bool			isOrigLit	()	const	{ return origlit_; }
	const Lit&		getPropLit	()	const	{ return proplit_; }
	Lit				getOrigLit	()	const	{ return origlit_?proplit_:not proplit_; }
	const Weight&	getWeight	()	const 	{ return weight_; }
	int				getAggIndex	()	const;

	void			propagate	();
};

class AggReason {
private:
	Disjunction 	explanation;
	bool 		hasclause;

public:
	AggReason(): explanation({}), hasclause(false){ }
	virtual ~AggReason() {}

	virtual const Agg&	getAgg			() 	const = 0;
	virtual Lit			getPropLit		()	const = 0;
	virtual Weight		getPropWeight	()	const = 0;
	virtual bool		isHeadReason	() 	const = 0;
	virtual bool		isInSet			()	const = 0;

    bool 		hasClause		()	const	{ return hasclause; }
    const Disjunction&	getClause	()	const	{ MAssert(hasClause()); return explanation; }
    void		setClause		(const Disjunction& c) {	explanation = c; hasclause = true; }
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
    Weight			getPropWeight	()	const	{ MAssert(false); return Weight(-1); }
    bool			isHeadReason	() 	const	{ return true; }
    bool			isInSet			()	const	{ MAssert(false); return false; }
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
    Lit				getPropLit		()	const	{ return inset?l:not l; }
    Weight			getPropWeight	()	const	{ return w; }
    bool			isHeadReason	() 	const	{ return false; }
    bool			isInSet			()	const	{ return inset; }
};

}

#endif /* AGGCOMB_HPP_ */
