#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <stdlib.h>
#include <string>

#include <iostream>

using namespace std;

namespace MINISAT{
	enum EqType{
		MEQ, MNEQ, ML, MG, MGEQ, MLEQ
	};
}

/* does not seem to work
std::ostream& operator<<(std::ostream& os, enum MINISAT::EqType c)
{
	switch(c){
	case MINISAT::MEQ: return os << "=";
	case MINISAT::MNEQ: return os << "~=";
	case MINISAT::MLEQ: return os << "=<";
	case MINISAT::MGEQ: return os << ">=";
	case MINISAT::MG: return os << ">";
	case MINISAT::ML: return os << "<";
	default: return os;
	}
}*/

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

	bool operator== (const Literal& lit) const {
		return this->lit == lit.lit;
	}

	bool operator< (const Literal& lit) const {
		return abs(this->lit) < abs(lit.lit);
	}
};

struct LW{
	Literal l;
	Weight w;

	LW(Literal l, Weight w): l(l), w(w){}
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

	//rest

	bool def, aggr, mnmz, cp; // True for those extensions that are being used.
	IDSEM sem;
	int nbmodels; //Find at least this number of models. If there are less models,
	//UNSAT will be returned (after finding the existing number)
	FINDCS defn_strategy; // Controls which propagation strategy will be used for definitions.                         (default always)
	MARKDEPTH defn_search; // Controls which search type will be used for definitions.                                  (default include_cs)
	SEARCHSTRAT ufs_strategy; //Which algorithm to use to find unfounded sets

	bool lparse;

	ECNF_mode() :
		random_var_freq(0.02), var_decay(1 / 0.95), polarity_mode(polarity_stored), verbosity(0),
		def(false), aggr(false), mnmz(false), cp(false), sem(WELLF), nbmodels(1),
		defn_strategy(always), defn_search(include_cs), ufs_strategy(breadth_first),
		lparse(false){
	}
};

class idpexception: public std::exception{
private:
	string mess;
public:
	/*idpexception(): std::exception(){
		strcpy (mess,"\n");
	}*/
	idpexception(const char* m): std::exception(){
		mess.append("Exception caught: ");
		mess.append(m);
	}

	~idpexception() throw(){

	}

	virtual const char* what() const throw(){
		return mess.c_str();
	}
};

#endif /*EXTERNALUTILS_HPP_*/
