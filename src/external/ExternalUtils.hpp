/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <string>

#include <map>
#include <vector>
#include <string>
#include <cstdlib>
#include <assert.h>

typedef unsigned int uint;

// Weight declaration and utilities

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

		friend std::istream& operator>>(std::istream& input, Weight& obj);

		std::string get_str() const{
			if(!inf){
				return w.get_str();
			}else{
				return pos?"+inf":"-inf";
			}
		}

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
	std::istream& operator>>(std::istream& input, Weight& obj);
	std::ostream& operator<<(std::ostream& output, const Weight& p);
	}
#else
	namespace MinisatID {
	#define NOARBITPREC
	typedef int Weight;
	//FAST, NO OVERFLOW SUPPORT
	}
#endif


namespace MinisatID {

	// Generic exception
	class idpexception: public std::exception{
	private:
		std::string mess;

	public:
		idpexception(std::string m): std::exception(), mess(m){		}
		idpexception(const char* m): std::exception(){
			mess.append(m);
		}

		~idpexception() throw(){}

		virtual const char* what() const throw(){
			return mess.c_str();
		}
	};

	Weight posInfinity();
	Weight negInfinity();

	std::string toString(const Weight& w);

	// Comparison operator
	enum EqType{ MEQ, MNEQ, ML, MG, MGEQ, MLEQ };

	// Aggregate specification operators
	enum AggType 	{ SUM, PROD, MIN, MAX, CARD }; 	// Type of aggregate concerned
	enum AggSign 	{ AGGSIGN_UB, AGGSIGN_LB}; 	// Sign of the bound of the aggregate
	enum AggSem 	{ COMP, DEF, IMPLICATION };	// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

	// Definitional options
	enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
	enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
												// when a guaranteed cycle-free justification is used!
	enum DEFSEARCHSTRAT { breadth_first, depth_first }; // Unfounded set search strategy
	enum DEFSEM { DEF_STABLE, DEF_WELLF, DEF_COMP }; 	// Definitional semantics

	enum POLARITY {
		POL_TRUE,
		POL_FALSE,
		POL_STORED,
		POL_RAND
	}; // SAT-solver polarity option

	enum INPUTFORMAT 	{ FORMAT_FODOT, FORMAT_ASP, FORMAT_OPB};
	enum OUTPUTFORMAT 	{ TRANS_FODOT, TRANS_ASP, TRANS_PLAIN };

	// Structure containing general options for the solvers
	class SolverOption {
			//TODO prevent unauthorised access by getters and setters (e.g. primesfile should NEVER be accessed directly
	public:
		INPUTFORMAT 	format;
		OUTPUTFORMAT 	transformat;
		int 			verbosity;
		int 			randomseed;
		int 			nbmodels;
		bool 			printcnfgraph;
		DEFSEM 			defsem;
		DEFSEARCHSTRAT 	ufs_strategy;
		DEFFINDCS 		defn_strategy;
		DEFMARKDEPTH 	defn_search;
		bool			checkcyclefreeness;
		int 			idclausesaving, aggclausesaving;
		bool 			selectOneFromUFS;
		bool 			pbsolver;
		double			watchesratio;
		bool			useaggheur;
		std::string 	primesfile;
		bool 			remap;
		double 			rand_var_freq, var_decay;
		POLARITY 		polarity;
		bool 			bumpaggonnotify, bumpidonstart;
		bool			subsetminimizeexplanation, asapaggprop;
		long 			ufsvarintrothreshold;

		SolverOption();

		bool 		verifyOptions() const;
		std::string	getPrimesFile() const;
		void print(std::ostream& stream) const;
	};

	enum PrintModel	{PRINT_ALL, PRINT_BEST, PRINT_NONE};
	enum SaveModel	{SAVE_ALL, SAVE_BEST, SAVE_NONE};
	enum Inference	{PROPAGATE, MODELEXPAND };

	class ModelExpandOptions{
	public:
		PrintModel		printmodels;
		SaveModel		savemodels;
		Inference		search;
		int 			nbmodelstofind;

		ModelExpandOptions():
				printmodels(PRINT_ALL), savemodels(SAVE_ALL), search(MODELEXPAND),
				nbmodelstofind(0)
			{}
	};
}

namespace MinisatID {

// Generic atom and literal structurese

class Atom{
private:
	int atom; //Important: because of mutual exclusion of const members and a clean assignment operator, i did not make this constant, but semantically it should be

public:
	explicit Atom(int a): atom(a){ }
	int		getValue	() 				const { return atom; }

	bool operator==	(const Atom& a) const { return atom==a.atom; }
	bool operator<	(const Atom& a) const { return atom<a.atom; }
};

class Literal{
private:
	int lit;

public:
	//@pre: a is positive
	explicit Literal(int a, bool s = false): lit(s?-a:a){ assert(a>=0); }
	explicit Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){ assert(a.getValue()>=0); }

	int		getValue()						const { return lit; }
	Atom 	getAtom() 						const { return Atom(lit<0?-lit:lit); }
	bool 	hasSign() 						const { return lit<0; }
	bool 	operator== (const Literal& l) 	const { return lit == l.lit; }
	bool 	operator< (const Literal& l) 	const {	return abs(lit) < abs(l.lit); }
	Literal operator~()						const { return Literal(getAtom(), lit>0?true:false); }
};

// A class representing a tuple of a literal and an associated weight
struct WLtuple{
	const Literal l;
	const Weight w;

	WLtuple(const Literal& l, const Weight& w): l(l), w(w){ }
	WLtuple operator=(const WLtuple& lw) const { return WLtuple(lw.l, lw.w); }
};

typedef std::vector<Literal> literallist;
typedef std::vector<std::vector<Literal> > modellist;

class Disjunction{
public:
	std::vector<Literal> literals;
};

class DisjunctionRef{
public:
	const std::vector<Literal>& literals;

	DisjunctionRef(const std::vector<Literal>& lits): literals(lits){}
};

class Equivalence{
public:
	bool conj;
	Literal	head;
	std::vector<Literal> literals;

	Equivalence():head(0){}
};

class Rule{
public:
	Atom head;
	std::vector<Literal> body;
	bool conjunctive;
	int definitionID;

	Rule(): head(0){}
};

class Set{
public:
	int setID;
	std::vector<Literal> literals;
};

class WSet{
public:
	int setID;
	std::vector<Literal> literals;
	std::vector<Weight> weights;
};

class WLSet{
public:
	int setID;
	std::vector<WLtuple> wl;
};

class Aggregate{
public:
	Atom head;
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
	AggSem sem;
	int defID; //Only relevant if defined aggregate

	Aggregate(): head(0){}
};

class MinimizeOrderedList{
public:
	std::vector<Literal> literals;
};

class MinimizeSubset{
public:
	std::vector<Literal> literals;
};

class MinimizeAgg{
public:
	Atom head;
	int setid;
	AggType type;

	MinimizeAgg(): head(0){}
};

struct CPIntVar{
	uint varID;
	int minvalue, maxvalue;
};

struct CPBinaryRel{
	Atom head;
	uint varID;
	EqType rel;
	int bound;

	CPBinaryRel(): head(0){}
};

struct CPBinaryRelVar{
	Atom head;
	uint lhsvarID, rhsvarID;
	EqType rel;

	CPBinaryRelVar(): head(0){}
};


struct CPSum{
	Atom head;
	std::vector<uint> varIDs;
	EqType rel;
	int bound;

	CPSum(): head(0){}
};

struct CPSumWeighted{
	Atom head;
	std::vector<uint> varIDs;
	std::vector<int> weights;
	EqType rel;
	int bound;

	CPSumWeighted(): head(0){}
};

struct CPSumWithVar{
	Atom head;
	std::vector<uint> varIDs;
	EqType rel;
	uint rhsvarID;

	CPSumWithVar(): head(0){}
};

struct CPSumWeightedWithVar{
	Atom head;
	std::vector<uint> varIDs;
	std::vector<int> weights;
	EqType rel;
	uint rhsvarID;

	CPSumWeightedWithVar(): head(0){}
};

struct CPCount{
	std::vector<uint> varIDs;
	int eqbound;
	EqType rel;
	uint rhsvar;
};

struct CPAllDiff{
	std::vector<uint> varIDs;
};

class ForcedChoices{
public:
	std::vector<Literal> forcedchoices;
};

class RigidAtoms{
public:
	std::vector<Atom> rigidatoms;
};

class SubTheory{
public:
	int child;
	Literal head;

	SubTheory():head(0){}
};

}

#endif /*EXTERNALUTILS_HPP_*/
