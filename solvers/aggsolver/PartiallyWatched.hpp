/*
 * PartiallyWatched.hpp
 *
 *  Created on: Sep 14, 2010
 *      Author: broes
 */

#ifndef PARTIALLYWATCHED_HPP_
#define PARTIALLYWATCHED_HPP_

#include "solvers/utils/Utils.hpp"

#include "solvers/aggsolver/AggComb.hpp"

class AggSolver;
namespace Aggrs{
	class Agg;
	class AggSet;

	typedef Agg* pagg;
	typedef vector<Agg*> vpagg;
	typedef AggSet* pset;

	class CalcAgg;
	typedef CalcAgg aggs;
	typedef aggs* paggs;

	class Propagator;
	typedef Propagator comb;
	typedef comb* pcomb;

	class Watch;
	typedef Watch* pw;
	typedef vector<pw> vpw;
	typedef vector<vpw> vvpw;

	class PropagationInfo;
	typedef vector<PropagationInfo> vprop;
}

///////
// DECLARATIONS
///////
namespace Aggrs{

class PWAgg: public Propagator {
public:
	PWAgg(paggs agg);
	virtual ~PWAgg(){};

	virtual void 	backtrack		(const Watch& w) {}
};

/*class CardPWAgg: public PWAgg, public virtual CardAggT {
private:
	vector<Lit> nf, nfex, nt, ntex;
public:
	CardPWAgg(paggs agg);
	virtual ~CardPWAgg(){};

	virtual rClause propagate		(const Lit& p, const Watch& w);
	virtual rClause propagate		(const Agg& agg);
	virtual void 	backtrack		(const Agg& agg);
    virtual void 	getExplanation	(vec<Lit>& lits, const AggReason& ar) const;

	virtual paggs 	initialize		(bool& unsat);

	bool isNonFalse(int number, int setsize, Bound sign, Weight bound) const;
	bool isNonTrue(int number, int setsize, Bound sign, Weight bound) const;
};*/

enum watchset { NF, NFEX, NT, NTEX, INSET };

class PWatch: public Watch{
private:
	mutable watchset w;
	mutable bool	inuse;
public:
	PWatch(paggs agg, int index, watchset w): Watch(agg, index, true, true), w(w), inuse(false){

	}

	watchset getWatchset() const { return w; }
	void	setWatchset(watchset w2) const { w = w2; }
	bool	isInUse() const { return inuse; }
	void	setInUse(bool used) const { inuse = used; }
};

struct ToWatch{
	PWatch* _watch;
	WL		_wl;

	ToWatch(paggs agg, const WL& wl): _wl(wl){
		_watch = new PWatch(agg, -1, INSET);
	}
	~ToWatch(){
		delete _watch;
	}

	const WL& 	wl		() const { return _wl; }
	const Lit& 	lit		() const { return _wl.getLit(); }
	PWatch* 	watch	() const { return _watch; }
};

typedef ToWatch tw;
typedef tw* ptw;
typedef vector<ptw> vptw;

class CardPWAgg: public PWAgg, public virtual CardAggT {
private:
	vptw nf, nfex, setf; //setf contains all monotone versions of set literals
	vptw nt, ntex, sett; //sett contains all anti-monotone versions of set literals
	lbool headvalue;
	bool headpropagatedhere;

	vector<int> startsetf, startsett; //Vector mapping decision levels to indices where to start looking for replacement watches

public:
	CardPWAgg(paggs agg);
	virtual ~CardPWAgg();

	/*virtual void newDecisionLevel() { startsetf.push_back(startsetf[startsetf.size()-1]); startsett.push_back(startsett[startsett.size()-1]);
		//reportf("SetF size %d, Skipped %d\n", setf.size(), startsetf[startsetf.size()-1]);
		//reportf("SetT size %d, Skipped %d\n", sett.size(), startsett[startsett.size()-1]);
	}
	virtual void backtrackDecisionLevel() { startsetf.pop_back(); startsett.pop_back(); }*/
	vector<int>& start(watchset w);

	bool initializeNF();
	bool initializeNT();
	bool initializeNFL();
	bool initializeNTL();
	bool initializeEX(watchset w);

	void addWatchesToSolver(watchset w);
	void addWatchToSolver(watchset w, const vptw& set, vsize index);

	void addToWatchedSet(watchset w, vsize setindex);
	void removeWatches(watchset w);

	bool replace(vsize index, watchset w);

	virtual rClause 	propagate			(const Lit& p, pw w);
	virtual rClause 	propagate			(const Agg& agg);
	virtual void 		backtrack			(const Agg& agg);
    virtual void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) const;

	virtual void 		initialize			(bool& unsat, bool& sat);

	vptw& getSet(watchset w);
	vptw& getWatches(watchset w);
	bool checking(watchset w) const;
	bool isEX(watchset w) const { return w==NFEX || w==NTEX; }
	bool isF(watchset w) const { return w==NF || w==NFEX; }
};

//BASEDONCC: propagated because of too many monotone false / am true literals
//BASEDONCP: propagated because of too many monotone true / am false literals


/*
 * watchset	: the location of in which set the watch effectively resides
 * inuse 	: whether the watch is in the watch network
 * 		combination: if watchset==INSET, then the watch SHOULD be removed. This is checked the first time the watch is activated
 * pos		: how the value of the weight should be treated: as IN the set, OUT the set or UNKN (depending on evaluting min or max)
 * watchneg	: if true, the negation of the wl literal is the effective watch, otherwise the wl literal itself
 */

enum POSS {POSINSET, POSOUTSET, POSSETUNKN};

class GenPWatch: public Watch{
private:
			watchset _w;
			bool	_inuse;
	const 	WL		_wl;
	const 	bool	_watchneg;
			POSS	_setpos;
	const 	bool	_mono;
public:
	GenPWatch(paggs agg, const WL& wl, bool watchneg, bool mono):
		Watch(agg, -1, true, true),
		_w(INSET),
		_inuse(false),
		_wl(wl),
		_watchneg(watchneg),
		_setpos(POSSETUNKN),
		_mono(mono){

	}

	bool 		isMonotone	()	const 	{ return _mono; }
	POSS		getPos		()	const	{ return _setpos; }
	void		setPos		(POSS p)	{ _setpos = p; }
	const WL& 	getWL		() 	const 	{ return _wl; }
	Lit			getWatchLit	() 	const 	{ return _watchneg?~_wl.getLit():_wl; }
	watchset 	getWatchset	() 	const 	{ return _w; }
	bool		isInUse		() 	const 	{ return _inuse; }
	void		setInUse	(bool used) { _inuse = used; }

	void		pushIntoSet(watchset w, vsize index) { setIndex(index); _w = w; }
	void		removedFromSet() { setIndex(-1); _w = INSET; _setpos = POSSETUNKN; }
};

typedef GenPWatch gpw;
typedef gpw* pgpw;
typedef vector<pgpw> vpgpw;


class GenPWAgg: public PWAgg, public virtual CardAggT{
private:
	vpgpw nf, setf; //setf contains all monotone versions of set literals
	vpgpw nt, sett; //sett contains all anti-monotone versions of set literals

	bool headprop; // true if <head> was derived from this aggregate

public:
	GenPWAgg(paggs agg);
	virtual ~GenPWAgg();

	bool isSatisfied(const Agg& agg, Weight value){
		return (agg.isLower() && value <= agg.getBound() ) || (agg.isUpper() && agg.getBound()<=value);
	}

	lbool 		isKnown(watchset w, const Agg& agg, const vpgpw& set, const vpgpw& set2);

	void 		initialize(bool& unsat, bool& sat);
	rClause 	reconstructSet(const Agg& agg, watchset w, pgpw watch, bool& propagations);

	void 		addToWatchedSet(watchset w, vsize index, POSS p);
	void 		removeWatchesFromSet(watchset w);
	void 		addWatchesToNetwork(watchset w);
	void 		addWatchToNetwork(pgpw watch);

	rClause 	propagate			(const Lit& p, pw w);
	rClause 	propagate			(const Agg& agg);
	void 		backtrack			(const Agg& agg);
    void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) const;

	vpgpw& getSet(watchset w);
	vpgpw& getWatches(watchset w);
	bool checking(watchset w) const;
	bool isNonFalseCheck(watchset w) const { return w==NF; }
};

void printWatches(AggSolver* const solver, const vvpw& tempwatches);

}

#endif /* PARTIALLYWATCHED_HPP_ */
