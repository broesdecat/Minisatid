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
	typedef std::vector<Watch*> vpw;
	typedef std::vector<std::vector<Watch*> > vvpw;

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
			bool	_innws; //True if it is in NWS, false if it is in WS
			bool	_innet; //True if it is in the watch network
	const 	WL		_wl;
	const 	bool	_watchneg;
			int 	_index; //-1 if _innws
public:
	GenPWatch(TypedSet* set, const WL& wl, bool watchneg, vsize index):
		Watch(set, wl),
		_innws(true),
		_innet(false),
		_wl(wl),
		_watchneg(watchneg),
		_index(index){
	}

	int getIndex() const { return _index; }
	void setIndex(int c) { _index = c; }

	bool 		isMonotone	()	const 	{ return _watchneg; }
	const WL& 	getWL		() 	const 	{ return _wl; }
	Lit			getWatchLit	() 	const 	{ return _watchneg?~_wl.getLit():_wl.getLit(); }
	bool		isInNetwork		() 	const 	{ return _innet; }
	void		addToNetwork	(bool used) { _innet = used; }

	bool		isInWS	()	const	{ return !_innws; }
	void		moveToWSPos(vsize index) { setIndex(index); _innws=false; }
	void		moveToNWSPos(vsize index) { setIndex(index); _innws = true; }
};

typedef GenPWatch* pgpw;
typedef std::vector<GenPWatch*> vpgpw;

class GenPWAgg: public PWAgg{
private:
	vpgpw ws, nws, _newwatches;
	Weight genmin, genmax; //min and max values on the empty interpretation
	Agg const * worstagg;

public:
	GenPWAgg(TypedSet* set);
	virtual ~GenPWAgg();

	Weight		getValue	()	const;

	void		calculateBoundsOfWatches(Weight& min, Weight& max, Weight& knownmin, Weight& knownmax, GenPWatch* largest);

	rClause 	reconstructSet(pgpw watch, bool& propagations, Agg const * propagg);
	void 		genWatches(vsize& i, const Agg& agg, Weight& min, Weight& max, Weight& knownmin, Weight& knownmax, GenPWatch*& largest, std::vector<GenPWatch*>& watchestoadd);

	rClause 	checkPropagation(bool& propagations, Weight& min, Weight& max, Agg const * agg);
	rClause 	checkOneAggPropagation(bool& propagations, const Agg& agg, const Weight& min, const Weight& max);

	void 		addToWatchedSet(GenPWatch* watch);
	void 		removeFromWatchedSet(pgpw pw);
	void 		addWatchesToNetwork();
	void 		addWatchToNetwork(pgpw watch);

	void 		initialize		(bool& unsat, bool& sat);
	rClause 	propagate		(const Lit& p, Watch* w, int level);
	rClause 	propagate		(int level, const Agg& agg, bool headtrue);
	rClause		propagateAtEndOfQueue(int level);
	void		backtrack		(int nblevels, int untillevel){};
    void 		getExplanation	(vec<Lit>& lits, const AggReason& ar);

    const vpgpw&	getNWS() const { return nws; }
    const vpgpw&	getWS() const { return ws; }
	vpgpw& 		getNWS() { return nws; }
	vpgpw& 		getWS() { return ws; }

	double 		testGenWatchCount();
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

}

}

#endif /* PARTIALLYWATCHED_HPP_ */
