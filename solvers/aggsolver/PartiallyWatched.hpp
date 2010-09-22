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

	class PropagationInfo;
	typedef vector<PropagationInfo> vprop;

	typedef vector<void*>::size_type vsize;
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

	const WL& wl() const { return _wl; }
	const Lit& lit() const { return _wl.getLit(); }
	PWatch* watch() const { return _watch; }
};

typedef ToWatch* ptw;
typedef vector<ptw> vptw;

class CardPWAgg: public PWAgg, public virtual CardAggT {
private:
	vptw nf, nfex, setf; //setf contains all monotone versions of set literals
	vptw nt, ntex, sett; //sett contains all anti-monotone versions of set literals
	lbool headvalue;
	bool headpropagatedhere;

public:
	CardPWAgg(paggs agg);
	virtual ~CardPWAgg(){};

	bool initializeNF();
	bool initializeNT();
	bool initializeNFL();
	bool initializeNTL();
	bool initializeEX(watchset w);

	void addWatchesToSolver(watchset w);
	void addWatchToSolver(watchset w, const vptw& set, int index);

	void addToWatchedSet(watchset w, int setindex);
	void removeWatches(watchset w);

	bool replace(vsize index, watchset w);

	virtual rClause 	propagate			(const Lit& p, const Watch& w);
	virtual rClause 	propagate			(const Agg& agg);
	virtual void 		backtrack			(const Agg& agg);
    virtual void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) const;
    		bool		assertedBefore(const Var& l, const Var& p) const;

	virtual void 		initialize			(bool& unsat, bool& sat);

	vptw& getSet(watchset w);
	vptw& getWatches(watchset w);
	bool checking(watchset w) const;
	bool isEX(watchset w) const { return w==NFEX || w==NTEX; }
	bool isF(watchset w) const { return w==NF || w==NFEX; }
};

}

#endif /* PARTIALLYWATCHED_HPP_ */
