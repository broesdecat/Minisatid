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


///////
// Debug information
///////

#define report(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

namespace MinisatID {

///////
// Measuring cpu time
///////

//In elapsed seconds, making abstraction of other processes running on the system
double cpuTime(void);

///////
// Generic system exception
///////

class idpexception: public std::exception{
private:
	std::string mess;

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
// Comparison operators
///////

enum EqType{ MEQ, MNEQ, ML, MG, MGEQ, MLEQ };

}

///////
// Weight declaration and utilities
///////

#ifdef GMP
	#include "gmpxx.h"

	namespace MinisatID {
	#define GMPWEIGHT
	typedef mpz_class Weight;
	//MEDIUM SPEED, NEED LIB INSTALLED, MUCH FASTER THAN BIGINT FOR ARBITRARY PREC, OVERFLOW SUPPORT
	}
#else
#ifdef BIGINT
	#include "BigInteger.hh"
	#include "BigIntegerUtils.hh"

	namespace MinisatID {
	#define BIGINTWEIGHT
	typedef BigInteger Weight;
	//SLOWEST, NO LIB NEEDED, OVERFLOW SUPPORT
	}
#else
	namespace MinisatID {
	#define INTWEIGHT
	typedef int Weight;
	//FASTEST, NO OVERFLOW SUPPORT
	}
#endif
#endif

namespace MinisatID {

Weight negInfinity();
Weight posInfinity();

std::string printWeight(const Weight& w);

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
	int lit;

public:
	//@pre: a is positive
	Literal(int a, bool s = false): lit(s?-a:a){ assert(a>=0); }
	Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){ assert(a.getValue()>=0); }

	Atom 	getAtom() 						const { return Atom(lit<0?-lit:lit); }
	bool 	getSign() 						const { return lit<0; }
	bool 	operator== (const Literal& l) 	const { return lit == l.lit; }
	bool 	operator< (const Literal& l) 	const {	return abs(lit) < abs(l.lit); }
};

// A class representing a tuple of a literal and an associated weight
struct WLtuple{
	const Literal l;
	const Weight w;

	WLtuple(const Literal& l, const Weight& w): l(l), w(w){ }
	WLtuple operator=(const WLtuple& lw) const { return WLtuple(lw.l, lw.w); }
};

///////
// Aggregate information
///////

enum AggType 	{ SUM, PROD, MIN, MAX, CARD }; 	// Type of aggregate concerned
enum AggSign 	{ UB, LB/*, BOTHBOUNDS*/ }; 	// Sign of the bound of the aggregate: the bound is an UpperBound
												// or LowerBound for the aggregate value
enum AggSem 	{ COMP, DEF };	// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

///////
// Definitional options
///////

enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
											// when a guaranteed cycle-free justification is used!
enum DEFSEARCHSTRAT { breadth_first, depth_first }; // Unfounded set search strategy
enum DEFSEM { STABLE, WELLF }; 				// Definitional semantics

///////
// SAT-solver options
///////

// Class to manage a file
class FileR {
private:
	bool opened, writeaccess, stream;
	const char* name; // if not a stream
	FILE* file;

	FileR(const FileR &);
	FileR & operator=(const FileR &);

public:
	FileR(FILE* file) : //for streams
			opened(false), writeaccess(true), stream(true), file(file) {	}
	FileR(const char* name, bool write) :
			opened(false), writeaccess(write), stream(false), name(name), file(NULL) {
		openFile();
	}

	~FileR() {
		if (opened) {
			fclose(file);
		}
	}

	void close() {
		if (opened) {
			opened = false;
			fclose(file);
		}
	}
	FILE* getFile() {
		openFile();
		return file;
	}

private:
	void openFile(){
		if(!opened && !stream){
			file = fopen(name, writeaccess?"wb":"r");
			if (file == NULL) {
				char s[100];
				sprintf(s, "`%s' is not a valid filename or not readable.\n", name);
				throw idpexception(s);
			}
			opened = true;
		}
	}
};

void setInputFileUrl(const char* url);
const char* getInputFileUrl();
FILE* getInputFile();
void setOutputFileUrl(const char* url);
FILE* getOutputFile();
void closeInput();
void closeOutput();

enum POLARITY {
	polarity_true = 0,
	polarity_false = 1,
	polarity_stored = 2,
	polarity_rnd = 3
}; // SAT-solver polarity option

// Structure containing all options used to run the solver.
struct ECNF_mode {
	//INPUT OPTIONS
	double random_var_freq, var_decay;
	POLARITY polarity_mode;
	int verbosity;

	int nbmodels; //Try to find at most this number of models
	DEFSEM sem; //Definitional semantics to be used
	DEFFINDCS defn_strategy; // Controls which propagation strategy will be used for definitions.                         (default always)
	DEFMARKDEPTH defn_search; // Controls which search type will be used for definitions.                                  (default include_cs)
	DEFSEARCHSTRAT ufs_strategy; //Which algorithm to use to find unfounded sets

	bool lparse;
	bool pb;
	bool remap;  //Whether he should remap the atom values from the input to fill up gaps in the numbering
	bool pw;	//use partially watched agg structures or not.
	bool randomize; // use random seed initialization for the SAT-solver
	bool disableheur; // turn off the heuristic of the sat solver, allowing more predictable behavior
	int idclausesaving; //0 = on propagation add clause to store, 1 = on propagation, generate explanation and save it, 2 = on propagation, generate reason and save it
	int aggclausesaving; //0 = on propagation add clause to store, 1 = on propagation, generate explanation and save it, 2 = on propagation, generate reason and save it

	bool printcnfgraph;

	//rest
	bool def, aggr, mnmz, cp; // True for those extensions that are being used.

	ECNF_mode() :
		random_var_freq(0.02),
		var_decay(1 / 0.95),
		polarity_mode(polarity_stored),
		verbosity(0),
		nbmodels(1),
		sem(WELLF),
		defn_strategy(always),
		defn_search(include_cs),
		ufs_strategy(breadth_first),
		lparse(false),
		pb(false),
		remap(false),
		pw(true),
		randomize(false),
		disableheur(false),
		idclausesaving(0),
		aggclausesaving(2),
		printcnfgraph(false),
		def(false),
		aggr(false),
		mnmz(false),
		cp(false){
	}
};

}

#endif /*EXTERNALUTILS_HPP_*/
