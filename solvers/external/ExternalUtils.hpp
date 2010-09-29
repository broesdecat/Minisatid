//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <stdlib.h>
#include <string>
#include <assert.h>

#include <iostream>
#include <map>
#include <vector>

using namespace std;

#define reportf(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

///////
// Comparison operators
///////

namespace MINISAT{
	enum EqType{ MEQ, MNEQ, ML, MG, MGEQ, MLEQ };
}

///////
// Weight declaration
///////

#ifdef GMP
	#define GMPWEIGHT
	#include "gmpxx.h"
	typedef mpz_class Weight;
	//MEDIUM SPEED, NEED LIB INSTALLED, MUCH FASTER THAN BIGINT FOR ARBITRARY PREC, OVERFLOW SUPPORT
#else
#ifdef BIGINT
	#define BIGINTWEIGHT
	#include "BigInteger.hh"
	#include "BigIntegerUtils.hh"
	typedef BigInteger Weight;
	//SLOWEST, NO LIB NEEDED, OVERFLOW SUPPORT
#else
	#define INTWEIGHT
	typedef int Weight;
	//FASTEST, NO OVERFLOW SUPPORT
#endif
#endif

Weight negInfinity();
Weight posInfinity();

string printWeight(const Weight& w);

///////
// Generic system exception
///////

class idpexception: public std::exception{
private:
	string mess;
public:
	idpexception(const char* m): std::exception(){
		mess.append("Exception caught: ");
		mess.append(m);
	}

	~idpexception() throw(){}

	virtual const char* what() const throw(){
		return mess.c_str();
	}
};

///////
// Aggregate information
///////

enum AggType 	{ SUM, PROD, MIN, MAX, CARD }; 	// Type of aggregate concerned
enum AggSign 	{ UB, LB/*, BOTHBOUNDS*/ }; 	// Sign of the bound of the aggregate: the bound is an UpperBound
												// or LowerBound for the aggregate value
enum AggSem 	{ COMP, DEF };	// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

///////
// Generic atom and literal structures
///////

class Atom{
private:
	int atom; //Important: because of mutual exclusion of const members and a clean assignment operator, i did not make this constant, but semantically it should be

public:
	explicit Atom(int a): atom(a){ }
	int		getValue	() 				const { return atom; }
};

class Literal{
private:
	const int lit;

public:
	//@pre: a is positive
	Literal(int a, bool s = false): lit(s?-a:a){ assert(a>=0); }
	Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){ assert(a.getValue()>=0); }

	Literal	operator=	(const Literal& l)	const { return Literal(l.getAtom(), l.getSign()); }
	Atom 	getAtom() 						const { return Atom(lit<0?-lit:lit); }
	bool 	getSign() 						const { return lit<0; }
	bool 	operator== (const Literal& lit) const { return this->lit == lit.lit; }
	bool 	operator< (const Literal& lit) 	const {	return abs(this->lit) < abs(lit.lit); }
};

// A class representing a tuple of a literal and an associated weight
struct LW{
	const Literal l;
	const Weight w;

	LW(const Literal& l, const Weight& w): l(l), w(w){ }
	LW operator=(const LW& lw) const { return LW(lw.l, lw.w); }
};

///////
// SYSTEM OPTIONS
///////

enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
											// when a guaranteed cycle-free justification is used!
enum DEFSEARCHSTRAT { breadth_first, depth_first }; // Unfounded set search strategy
enum DEFSEM { STABLE, WELLF }; 				// Definitional semantics

enum POLARITY {
	polarity_true = 0,
	polarity_false = 1,
	polarity_stored = 2,
	polarity_rnd = 3
}; // SAT-solver polarity option

/*
 * Variabele - naam - mogelijke waarden - beschrijving
 *
 * mapping naam->variabele
 * lijst variabelen
 */

/*struct ECNF_mode;

struct IntOption{
	const string naam;
	const int min, max;
	const string description;

	IntOption(string naam, int min, int max, string description):naam(naam), min(min), max(max), description(description){}
	IntOption(ECNF_mode& mode, string naam, int min, int max, string description);
	IntOption operator=(const IntOption& opt){
		return IntOption(opt.naam, opt.min, opt.max, opt.description);
	}

	void printHelp(){
		reportf("    -%s=<I> %s: <I>\\in[%d, %d].\n", naam.c_str(), description.c_str(), min, max);
	}
};*/

// Structure containing all options used to run the solver.
struct ECNF_mode {
	//IntOption vareen;
	/*map<string, IntOption> mapping;
	vector<IntOption> variabelen;

	void addVar(const IntOption& opt, string naam);*/

	double random_var_freq, var_decay;
	POLARITY polarity_mode;
	int verbosity;

	//rest
	bool def, aggr, mnmz, cp; // True for those extensions that are being used.
	DEFSEM sem;
	int nbmodels; //Find at least this number of models. If there are less models,
	//UNSAT will be returned (after finding the existing number)
	DEFFINDCS defn_strategy; // Controls which propagation strategy will be used for definitions.                         (default always)
	DEFMARKDEPTH defn_search; // Controls which search type will be used for definitions.                                  (default include_cs)
	DEFSEARCHSTRAT ufs_strategy; //Which algorithm to use to find unfounded sets

	bool lparse;
	bool pb;
	bool remap;  //Whether he should remap the atom values from the input to fill up gaps in the numbering
	bool pw;	//use partially watched agg structures or not.
	bool randomize; // use random seed initialization for the SAT-solver
	bool disableheur; // turn off the heuristic of the sat solver, allowing more predictable behavior

	ECNF_mode() :
		random_var_freq(0.02),
		var_decay(1 / 0.95),
		polarity_mode(polarity_stored),
		verbosity(0),
		def(false),
		aggr(false),
		mnmz(false),
		cp(false),
		sem(WELLF),
		nbmodels(1),
		defn_strategy(always),
		defn_search(include_cs),
		ufs_strategy(breadth_first),
		lparse(false),
		pb(false),
		remap(false),
		pw(true),
		randomize(false),
		disableheur(false)
		/*vareen(*this, "vareen", 0, 5, "Dit is een variabele")*/{
	}

	void printUsage();
	void parseCommandline(int& argc, char** argv);
};

#endif /*EXTERNALUTILS_HPP_*/

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
