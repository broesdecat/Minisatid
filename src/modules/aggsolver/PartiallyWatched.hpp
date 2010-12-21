#ifndef PARTIALLYWATCHED_HPP_
#define PARTIALLYWATCHED_HPP_

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

class AggSolver;
namespace Aggrs{
	class Agg;
	typedef Agg* pagg;
	typedef std::vector<Agg*> vpagg;
	class TypedSet;

	class Propagator;
	typedef Propagator comb;
	typedef comb* pcomb;

	class Watch;
	typedef Watch* pw;
	typedef std::vector<pw> vpw;
	typedef std::vector<vpw> vvpw;

	class PropagationInfo;
	typedef std::vector<PropagationInfo> vprop;
}

///////
// DECLARATIONS
///////
namespace Aggrs{

class PWAgg: public Propagator {
public:
	PWAgg(TypedSet* set);
	virtual ~PWAgg(){};

	virtual void 	backtrack		(const Watch& w) {}
};

//BASEDONCC: propagated because of too many monotone false / am true literals
//BASEDONCP: propagated because of too many monotone true / am false literals


/*
 * WATCHSET	: the location of in which set the watch effectively resides
 * inuse 	: whether the watch is in the watch network
 * 		combination: if WATCHSET==INSET, then the watch SHOULD be removed. This is checked the first time the watch is activated
 * pos		: how the value of the weight should be treated: as IN the set, OUT the set or UNKN (depending on evaluting min or max)
 * watchneg	: if true, the negation of the wl literal is the effective watch, otherwise the wl literal itself
 */

class GenPWatch: public Watch{
private:
			bool	_inset;
			bool	_inuse;
	const 	WL		_wl;
	const 	bool	_watchneg;
			int 	_index;
public:
	GenPWatch(TypedSet* set, const WL& wl, bool watchneg):
		Watch(set, wl),
		_inset(true),
		_inuse(false),
		_wl(wl),
		_watchneg(watchneg),
		_index(-1){
	}

	int getIndex() const { return _index; }
	void setIndex(int c) { _index = c; }

	bool 		isMonotone	()	const 	{ return _watchneg; }
	const WL& 	getWL		() 	const 	{ return _wl; }
	Lit			getWatchLit	() 	const 	{ return _watchneg?~_wl.getLit():_wl.getLit(); }
	bool		isInUse		() 	const 	{ return _inuse; }
	void		setInUse	(bool used) { _inuse = used; }
	bool		isWatched	()	const	{ return !_inset; }

	void		pushIntoSet(vsize index) { /*setIndex(index);*/ _inset=false; }
	void		removedFromSet() { /*setIndex(-1);*/ _inset = true; }
};

typedef GenPWatch* pgpw;
typedef std::vector<GenPWatch*> vpgpw;

class GenPWAgg: public PWAgg{
private:
	vpgpw ws, nws;
	Weight genmin, genmax; //min and max values on the empty interpretation

public:
	GenPWAgg(TypedSet* set);
	virtual ~GenPWAgg();

	bool isSatisfied(const Agg& agg, const Weight& min, const Weight& max) const{
		if(agg.hasUB()){
			return min<=agg.getCertainBound();
		}else{ //LB
			return max>=agg.getCertainBound();
		}
	}

	void 		addValue(const Weight& weight, bool inset, Weight& min, Weight& max) const;
	void 		removeValue(const Weight& weight, bool inset, Weight& min, Weight& max) const;

	rClause 	reconstructSet(pgpw watch, bool& propagations);
	rClause 	reconstructSet(const Agg& agg, pgpw watch, bool& propagations);

	rClause 	checkPropagation(bool& propagations);

	void 		addToWatchedSet(vsize index);
	void 		removeFromWatchedSet(pgpw pw);
	void 		removeAllFromWatchedSet();
	void 		addWatchesToNetwork();
	void 		addWatchToNetwork(pgpw watch);

	void 		initialize		(bool& unsat, bool& sat);
	rClause 	propagate		(const Lit& p, Watch* w, int level);
	rClause 	propagate		(int level, const Agg& agg, bool headtrue);
	rClause		propagateAtEndOfQueue(int level);
	void		backtrack		(int nblevels, int untillevel){};
    void 		getExplanation	(vec<Lit>& lits, const AggReason& ar);

	vpgpw& 		getNWS() { return nws; }
	vpgpw& 		getWS() { return ws; }
};

class CardGenPWAgg: public GenPWAgg{
public:
	CardGenPWAgg(TypedSet* set);
	virtual ~CardGenPWAgg(){}
};

class SumGenPWAgg: public GenPWAgg{
public:
	SumGenPWAgg(TypedSet* set);
	virtual ~SumGenPWAgg(){}
};

void printWatches(int verbosity, AggSolver* const solver, const vvpw& tempwatches);

}

}

#endif /* PARTIALLYWATCHED_HPP_ */
