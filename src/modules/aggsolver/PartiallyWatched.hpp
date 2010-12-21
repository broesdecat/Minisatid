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

enum WATCHSET { NF, NFEX, NT, NTEX, INSET };

class PWatch: public Watch{
private:
	mutable WATCHSET w;
	mutable bool	inuse;
	int 			index;
public:
	PWatch(TypedSet* set, const WL& wl, int index, WATCHSET w): Watch(set, wl), w(w), inuse(false), index(index){

	}

	int getIndex() const { return index; }
	void setIndex(int c) { index = c; }

	WATCHSET getWatchset() const { return w; }
	void	setWatchset(WATCHSET w2) const { w = w2; }
	bool	isInUse() const { return inuse; }
	void	setInUse(bool used) const { inuse = used; }

	const Lit& getLit() const { return getWL().getLit(); }
	const Weight& getWeight() const { return getWL().getWeight(); }
};

typedef PWatch tw;
typedef tw* ptw;
typedef std::vector<ptw> vptw;

class PWAgg: public Propagator {
public:
	PWAgg(TypedSet* set);
	virtual ~PWAgg(){};

	virtual void 	backtrack		(const Watch& w) {}
};

class CardPWAgg: public PWAgg{
private:
	vptw nf, nfex, setf; //setf contains all monotone versions of set literals
	vptw nt, ntex, sett; //sett contains all anti-monotone versions of set literals
	lbool headvalue;
	int headproplevel;
	bool headpropagatedhere;

	std::vector<int> startsetf, startsett; //std::vector mapping decision levels to indices where to start looking for replacement watches

public:
	CardPWAgg(TypedSet* agg);
	virtual ~CardPWAgg();

	virtual rClause 	propagate		(const Lit& p, Watch* w, int level);
	virtual rClause 	propagate		(int level, const Agg& agg, bool headtrue);
	virtual rClause		propagateAtEndOfQueue(int level){ return nullPtrClause; };
	virtual void		backtrack		(int nblevels, int untillevel);
    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar);

	virtual void 		initialize			(bool& unsat, bool& sat);

private:

	bool initializeNF();
	bool initializeNT();
	bool initializeNFL();
	bool initializeNTL();
	bool initializeEX(WATCHSET w);

	void addWatchesToSolver(WATCHSET w);
	void addWatchToSolver(WATCHSET w, const vptw& set, vsize index);

	void addToWatchedSet(WATCHSET w, vsize setindex);
	void removeWatches(WATCHSET w);

	bool replace(vsize index, WATCHSET w, const Lit& p);

	vptw& getSet(WATCHSET w);
	vptw& getWatches(WATCHSET w);
	bool checking(WATCHSET w) const;
	bool isEX(WATCHSET w) const { return w==NFEX || w==NTEX; }
	bool isF(WATCHSET w) const { return w==NF || w==NFEX; }
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
