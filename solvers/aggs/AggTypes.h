#ifndef AGGTYPES_H
#define AGGTYPES_H

#include <limits>
#include <vector>
#include <set>
#include <iostream>
#include <tr1/memory>

#include "SolverTypes.h"
#include "debug.h"

using namespace std;
using namespace tr1;

template <typename T>
string printWeight(const T& w);

#ifdef GMP
#define GMPWEIGHT
#include "gmpxx.h"
typedef mpz_class Weight;

//MEDIUM SPEED, NEED LIB INSTALLED, MUCH FASTER THAN BIGINT FOR ARBITRARY PREC
template <>
string printWeight<mpz_class>(const mpz_class& w);

#else
#ifdef BIGINT
#define BIGINTWEIGHT
#include "BigInteger.hh"
#include "BigIntegerUtils.hh"
typedef BigInteger Weight;
//SLOWEST, NO LIB NEEDED AND HAS OVERFLOW SUPPORT
template <>
string printWeight<BigInteger>(const BigInteger& w);

#else
#define INTWEIGHT
typedef int Weight;
//FIXME FAST, NOT CORRECT ON OVERFLOW
template <>
string printWeight<int>(const int& w);

#endif
#endif

namespace Aggrs{
class WLV;
typedef vector<WLV> lwlv;

class PropagationInfo;
typedef vector<PropagationInfo> lprop;

enum Occurrence {HEAD, POS, NEG};

class WLit {  // Weighted literal
private:
	Lit lit;
	Weight weight;

public:
    explicit WLit(const Lit& l, const Weight& w) : lit(l), weight(w) {}

    const Lit& 		getLit() 	const { return lit; }
    const Weight&	getWeight() const { return weight; }

    bool operator<	(const WLit& p)		 const { return weight < p.weight; }
    bool operator<	(const Weight& bound)const { return weight < bound; }
    bool operator==	(const WLit& p)		 const { return weight == p.weight && lit==p.lit; }
};

class WLV: public WLit{
private:
	lbool value;

public:
	explicit WLV(const Lit& l, const Weight& w, lbool value) : WLit(l, w), value(value) {}

	lbool	getValue() const 	{ return value; }
	void	setValue(lbool v) 	{ value = v; }
};

class PropagationInfo {	// Propagated literal
private:
	Lit 	lit;
	Weight 	weight;
	Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagate)
	Weight prevcertain, prevpossible; //values BEFORE the propagation was added

public:
    PropagationInfo(const Lit& l, const Weight& w, Occurrence t, const Weight& pc, const Weight& pv) :
    	lit(l), weight(w), type(t), prevcertain(pc), prevpossible(pv) {}

    const Lit& 			getLit()	const { return lit; }
    const Weight&		getWeight()	const { return weight; }
    const Occurrence& 	getType() 	const { return type; }
    const Weight& 		getPC()		const { return prevcertain; }
    const Weight& 		getPP()		const { return prevpossible; }
};
}

#endif /*AGGTYPES_H*/
