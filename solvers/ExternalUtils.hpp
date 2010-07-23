#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <stdlib.h>
#include <string>

using namespace std;

namespace MINISAT{
	enum EqType{
		MEQ, MNEQ, MLEQ, MGEQ, MG, ML
	};
}

class Atom{
private:
	int atom;

public:
	Atom(int a): atom(a){ 	}
	Atom(const Atom& a): atom(a.atom){ 	}

	int getValue() const { return atom; }
};

class Literal{
private:
	int lit;

public:
	//PRE: NON NEGATIVE ATOM
	Literal(int a, bool s = false): lit(s?-a:a){	}
	Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){	}

	Atom getAtom() const {return Atom(lit<0?-lit:lit); }
	bool getSign() const { return lit<0; }
};

enum FINDCS {
	always, adaptive, lazy
};
enum MARKDEPTH {
	include_cs, stop_at_cs
};
enum SEARCHSTRAT {
	breadth_first, depth_first
};
enum IDSEM {
	STABLE, WELLF
};

/**
 * The different possible types of definitions.
 * If a variable is NONDEFALL, no definition is associated with it.
 * If a variable is NONDEFPOS, a definition is associated with it, but there is no recursion through it in the POSITIVE dependency graph
 * 		but there might be recursion over negation (relevant for the well-founded model)
 */
enum DefType {
	NONDEFTYPE, DISJ, CONJ, AGGR
};
enum DefOcc {
	NONDEFOCC, POSLOOP, MIXEDLOOP, BOTHLOOP
};
enum UFS {
	NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK
};

enum AggrType {
	SUM, PROD, MIN, MAX, CARD
};

extern int verbosity;

enum MINIM {
	MNMZ, SUBSETMNMZ, SUMMNMZ, NONE
};

enum POLARITY {
	polarity_true = 0,
	polarity_false = 1,
	polarity_stored = 2,
	polarity_rnd = 3
};

struct ECNF_mode {
	double random_var_freq, var_decay;
	POLARITY polarity_mode;
	int verbosity;
	//verbosity

	//rest

	bool def, aggr, mnmz, cp; // True for those extensions that are being used.
	IDSEM sem;
	int nbmodels; //Find at least this number of models. If there are less models,
	//UNSAT will be returned (after finding the existing number)
	FINDCS defn_strategy; // Controls which propagation strategy will be used for definitions.                         (default always)
	MARKDEPTH defn_search; // Controls which search type will be used for definitions.                                  (default include_cs)
	SEARCHSTRAT ufs_strategy; //Which algorithm to use to find unfounded sets

	ECNF_mode() :
		random_var_freq(0.02), var_decay(1 / 0.95), polarity_mode(polarity_stored), verbosity(0),
		def(false), aggr(false), mnmz(false), cp(false), sem(WELLF), nbmodels(1),
		defn_strategy(always), defn_search(include_cs), ufs_strategy(breadth_first) {
	}
};

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
template <>
string printWeight<int>(const int& w);

#endif
#endif

class idpexception: public std::exception{
private:
	const char* mess;
public:
	idpexception(): std::exception(), mess(""){	}
	idpexception(const char* m): std::exception(), mess(m){	}

	virtual const char* what() const throw(){
		return mess;
	}
};

#endif /*EXTERNALUTILS_HPP_*/
