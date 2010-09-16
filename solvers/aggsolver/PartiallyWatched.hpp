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

class CardPWAgg: public PWAgg, public virtual CardAggT {
private:
	vector<WL> nf, nfex, setf;
	vector<WL> nt, ntex, sett;
	lbool headvalue;
public:
	CardPWAgg(paggs agg);
	virtual ~CardPWAgg(){};

	void addWatches(const vector<WL>& set, bool nf, bool ex) const;

	bool initializeNF();
	bool initializeNFex();
	bool replaceNF(vsize index);
	bool replaceNFex(vsize index);

	bool initializeNT();
	bool initializeNTex();
	bool replaceNT(vsize index);
	bool replaceNTex(vsize index);

	virtual rClause 	propagate			(const Lit& p, const Watch& w);
	virtual rClause 	propagate			(const Agg& agg);
	virtual void 		backtrack			(const Agg& agg);
    virtual void 		getExplanation		(vec<Lit>& lits, const AggReason& ar) const;

	virtual void 		initialize			(bool& unsat, bool& sat);

	bool checkingNF() 	const { return headvalue!=l_False; }
	bool checkingNFex() const { return headvalue==l_True; }
	bool checkingNT() 	const { return headvalue!=l_True; }
	bool checkingNTex() const { return headvalue==l_False; }
};

}

#endif /* PARTIALLYWATCHED_HPP_ */
