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

#include <string>
#include <assert.h>

#include <map>
#include <vector>
#include <string>


///////
// Debug information
///////

//FIXME move to print headers
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

///////
// Aggregate specification operators
///////

enum AggType 	{ SUM, PROD, MIN, MAX, CARD }; 	// Type of aggregate concerned
//FIXME correct notion of upper and lower bound!
enum AggSign 	{ AGGSIGN_UB, AGGSIGN_LB}; 	// Sign of the bound of the aggregate
enum AggSem 	{ COMP, DEF };	// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

}

///////
// Weight declaration and utilities
///////

#ifdef GMP
	#include "gmpxx.h"

	namespace MinisatID {
	class Weight{
	private:
		mpz_class w;
		bool inf, pos;
	public:
		Weight(): w(0), inf(false), pos(false){}
		Weight(int i): w(i), inf(false), pos(false){}
		Weight(long i): w(i), inf(false), pos(false){}
		Weight(mpz_class w): w(w), inf(false), pos(false){}
		Weight(bool posinf): w(0), inf(true), pos(posinf){}

		operator const mpz_class&() const { assert(!inf); return w; }

		std::string get_str() const{
			if(!inf){
				return w.get_str();
			}else{
				return pos?"+inf":"-inf";
			}
		}

		friend std::ostream& operator<<(std::ostream& output, const Weight& p);
		friend std::istream& operator>>(std::istream& input, Weight& obj);

		const Weight operator-() const {
			Weight w2(*this);
			w2.w = -w2.w;
			w2.pos=!w2.pos;
			return w2;
		}

		const Weight operator-(const Weight &other) const {
			return Weight(*this) -= other;
		}

		const Weight operator+(const Weight &other) const {
			return Weight(*this) += other;
		}

		const Weight operator*(const Weight &other) const {
			return Weight(*this) *= other;
		}

		const Weight operator/(const Weight &other) const {
			return Weight(*this) /= other;
		}

		Weight& operator+=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			}else{
				w += rhs.w;
			}
			return *this;
		}

		Weight& operator-=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:!rhs.pos;
				inf = true;
			}else{
				w -= rhs.w;
			}
			return *this;
		}

		Weight& operator*=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			}else{
				w *= rhs.w;
			}
			return *this;
		}

		Weight& operator/=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				if(inf){
					if(rhs.w<0){
						pos = !pos;
					}
				}else{
					w = 0;
					inf = false;
				}
			}else{
				w /= rhs.w;
			}
			return *this;
		}

		bool operator==(const Weight& weight) const{
			return w==weight.w && inf==weight.inf && pos==weight.pos;
		}

		bool operator!=(const Weight& weight) const{
			return !(*this==weight);
		}

		bool operator<(const Weight& weight) const {
			if(!inf && !weight.inf){
				return w < weight.w;
			}else if(inf){
				if(weight.inf){
					return false;
				}else{
					return !pos;
				}
			}else{//only weight is inf
				return weight.pos;
			}
		}

		bool operator<=(const Weight& weight) const{
			return *this==weight || *this<weight;
		}

		bool operator>(const Weight& weight) const{
			return !(*this<=weight);
		}

		bool operator>=(const Weight& weight) const{
			return !(*this<weight);
		}
	};
	Weight abs(const Weight& w);
	std::ostream& operator<<(std::ostream& output, const Weight& p);
	std::istream& operator>>(std::istream& input, Weight& obj);
	}
#else
	namespace MinisatID {
	#define NOARBITPREC
	typedef long Weight;
	//FAST, NO OVERFLOW SUPPORT
	}
#endif

namespace MinisatID {
Weight posInfinity();
Weight negInfinity();

std::string toString(const Weight& w);

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
// Definitional options
///////

enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
											// when a guaranteed cycle-free justification is used!
enum DEFSEARCHSTRAT { breadth_first, depth_first }; // Unfounded set search strategy
enum DEFSEM { DEF_STABLE, DEF_WELLF, DEF_COMP }; 				// Definitional semantics

enum POLARITY {
	POL_TRUE,
	POL_FALSE,
	POL_STORED,
	POL_RAND
}; // SAT-solver polarity option

enum INPUTFORMAT {FORMAT_FODOT, FORMAT_ASP, FORMAT_OPB};

// Structure containing general options for the solvers
class SolverOption {
public:
	INPUTFORMAT format;
	int verbosity;
	int nbmodels; //Try to find at most this number of models
	bool printcnfgraph;
	DEFSEM defsem;
	DEFSEARCHSTRAT ufs_strategy;
	DEFFINDCS defn_strategy;
	DEFMARKDEPTH defn_search;
	int idclausesaving, aggclausesaving;
	bool selectOneFromUFS;
	bool pbsolver;
	bool watchedagg;
	std::string primesfile;
	bool remap;
	double rand_var_freq, var_decay;
	POLARITY polarity;
	bool bumpaggonnotify, bumpidonstart, subsetminimizeexplanation, asapaggprop;
	long ufsvarintrothreshold;

	SolverOption();

	void print();
};

}

#endif /*EXTERNALUTILS_HPP_*/
