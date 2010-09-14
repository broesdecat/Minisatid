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

class CardPWAgg: public PWAgg, public virtual CardAggT {
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
};

}

#endif /* PARTIALLYWATCHED_HPP_ */
