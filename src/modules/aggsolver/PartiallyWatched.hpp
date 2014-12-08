/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PARTIALLYWATCHED_HPP_
#define PARTIALLYWATCHED_HPP_

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

class AggSolver;
class Agg;
typedef Agg* pagg;
typedef std::vector<Agg*> agglist;
class TypedSet;

class AggPropagator;
class Watch;

//BASEDONCC: propagated because of too many monotone false / am true literals
//BASEDONCP: propagated because of too many monotone true / am false literals

/*
 * WATCHSET	: the location of in which set the watch effectively resides
 * inuse 	: whether the watch is in the watch network
 * 		combination: if WATCHSET==INSET, then the watch SHOULD be removed. This is checked the first time the watch is activated
 * pos		: how the value of the weight should be treated: as IN the set, OUT the set or UNKN (depending on evaluting min or max)
 * watchneg	: if true, the negation of the wl literal is the effective watch, otherwise the wl literal itself
 */

class GenPWatch: public Watch {
private:
	bool _innws; //True if it is in NWS, false if it is in WS
	int _index; //-1 if _innws
public:
	GenPWatch(TypedSet* set, const WL& wl, bool watchneg, uint index) :
			Watch(set, watchneg?~wl.getLit():wl.getLit(), wl.getWeight(), not watchneg, true), _innws(true), _index(index) {
	}

	int getIndex() const {
		return _index;
	}
	void setIndex(int c) {
		_index = c;
	}
	bool isMonotone() const {
		return not isOrigLit();
	}
	WL getWL() const {
		return WL(getOrigLit(), getWeight());
	}
	Lit getWatchLit() const {
		return getPropLit();
	}

	bool isInWS() const {
		return !_innws;
	}
	void movedToOther() {
		_innws = !_innws;
	}
};

typedef GenPWatch* pgpw;
typedef std::vector<GenPWatch*> genwatchlist;

struct minmaxOptimAndPessBounds {
	minmaxBounds optim, pess;

	minmaxOptimAndPessBounds(const minmaxBounds& bounds) :
			optim(bounds), pess(bounds) {
	}
	minmaxOptimAndPessBounds(const Weight& optimmin, const Weight& optimmax, const Weight& pessmin, const Weight& pessmax) :
			optim(optimmin, optimmax), pess(pessmin, pessmax) {
	}
};

class GenPWAgg: public AggPropagator {
private:
	genwatchlist ws, nws, newwatches;
	minmaxBounds emptyinterpretbounds;
	Agg const * worstagg;
	std::vector<Watch*> proplist; // List of watches which still need to be propagated
	std::vector<std::pair<Atom, int> > backtracklist; // A list of which was the latest var which could be propagated at the associated level
	// If backtrack goes over such a level, need reconstruction
	bool certainlyreconstruct;

public:
	GenPWAgg(TypedSet* set);
	virtual ~GenPWAgg();

	virtual void internalInitialize(bool& unsat, bool& sat);
	virtual rClause reInitialize();
	virtual rClause propagateAtEndOfQueue();
	virtual void backtrack(int untillevel);
	virtual void getExplanation(litlist& lits, const AggReason& ar);

protected:
	virtual void propagate(int level, Watch* ws, int aggindex);
	virtual void propagate(const Lit& p, Watch* ws, int level);
	//rClause propagateAtEndOfQueue(Watch* w);

private:
	const genwatchlist& getNWS() const {
		return nws;
	}
	const genwatchlist& getWS() const {
		return ws;
	}
	genwatchlist& getNWS() {
		return nws;
	}
	genwatchlist& getWS() {
		return ws;
	}
	const genwatchlist& getStagedWatches() const {
		return newwatches;
	}
	genwatchlist& getStagedWatches() {
		return newwatches;
	}

	minmaxBounds calculatePessimisticBounds();
	void checkInitiallyKnownAggs(bool& unsat, bool& sat);

	Agg const* getWorstAgg() {
		return worstagg;
	}
	Agg* getAggWithMostStringentBound(bool includeunknown) const;

	minmaxBounds getBoundsOnEmptyInterpr() const {
		return emptyinterpretbounds;
	}
	void setBoundsOnEmptyInterpr(minmaxBounds bounds) {
		emptyinterpretbounds = bounds;
	}

	minmaxOptimAndPessBounds calculateBoundsOfWatches(GenPWatch*& largest) const;

	rClause reconstructSet(bool& propagations, Agg const * propagg);
	void genWatches(uint& i, const Agg& agg, minmaxOptimAndPessBounds& bounds, GenPWatch*& largest);

	void notifyFirstPropagation(const Lit& firstprop);

	rClause checkPropagation(bool& propagations, minmaxBounds& pessbounds, Agg const * agg);
	rClause checkHeadPropagationForAgg(bool& propagations, const Agg& agg, const minmaxBounds& pessbounds);

	void moveFromTo(GenPWatch* watch, genwatchlist& from, genwatchlist& to);
	void moveFromNWSToWS(GenPWatch* watch);
	void moveFromWSToNWS(pgpw pw);
	void resetStagedWatches(int startindex = 0);
	void addStagedWatchesToNetworkOnStable(rClause confl);
	void addWatchToNetwork(pgpw watch);

	const agglist& getAgg() const;
	const AggProp& getType() const;

	void stageWatch(GenPWatch* watch);

	void checkWatches() const;
};

double testGenWatchCount(const PCSolver& solver, const WLSet& set, const AggProp& type, const std::vector<TempAgg*> aggs);

}

#endif /* PARTIALLYWATCHED_HPP_ */
