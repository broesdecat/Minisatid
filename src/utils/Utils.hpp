/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef UTILS_H_
#define UTILS_H_

#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>

#include "GeneralUtils.hpp"
#include "satsolver/SATUtils.hpp"

typedef unsigned int uint;

namespace MinisatID {

typedef std::vector<Lit> litlist;
typedef std::vector<Var> varlist;
inline Lit  mkPosLit	(Var var) 	{ return mkLit(var, false); }
inline Lit  mkNegLit	(Var var) 	{ return mkLit(var, true); }
inline Lit 	operator!	(Lit p)		{ Lit q; q.x = p.x ^ 1; return q; }

class InterMediateDataStruct{
private:
	int offset;
	std::vector<int> seen;

public:
	InterMediateDataStruct(int nbvars, int offset):offset(offset){
		seen.resize(nbvars, 0);
	}

	bool hasElem(Var var) const { return var-offset>=0 && ((uint)var-offset)<seen.size(); }

	int& getElem(Var var) { return seen[var-offset]; }
	const int& getElem(Var var) const { return seen[var-offset]; }
};

enum PRIORITY { FAST = 0, SLOW = 1 };
enum EVENT { EV_PROPAGATE, EV_EXITCLEANLY, EV_CHOICE, EV_BACKTRACK, EV_DECISIONLEVEL, EV_PRINTSTATE, EV_PRINTSTATS,
			EV_FULLASSIGNMENT, EV_ADDCLAUSE, EV_REMOVECLAUSE, EV_SYMMETRYANALYZE, EV_BOUNDSCHANGE, EV_SYMMCHECK1, EV_SYMMCHECK2};

// General vector size type usable for any POINTER types!
typedef std::vector<void*>::size_type vsize;

bool 	isPositive(Lit l);
Lit 	createNegativeLiteral(Var i);
Lit 	createPositiveLiteral(Var i);

// Internal weighted literal

class WL {  // Weighted literal
private:
	Lit lit;
	Weight weight;

public:
    explicit 		WL(const Lit& l, const Weight& w) : lit(l), weight(w) {}

    const Lit& 		getLit		()	const { return lit; }
    const Weight&	getWeight	()	const { return weight; }

    bool 			operator<	(const WL& p)		 const { return weight < p.weight; }
    bool 			operator<	(const Weight& bound)const { return weight < bound; }
    bool 			operator==	(const WL& p)		 const { return weight == p.weight && lit==p.lit; }
};

typedef std::vector<WL> vwl;

//Compare WLs by their literals, placing same literals next to each other
bool compareWLByLits(const WL& one, const WL& two);

//Compare WLs by their weights
template<class T>
bool compareByWeights(const T& one, const T& two) {
      return one.getWeight() < two.getWeight();
}

bool compareWLByAbsWeights(const WL& one, const WL& two);

struct InnerModel{
	std::vector<Lit> litassignments;
	std::vector<VariableEqValue> varassignments;
};

struct InnerDisjunction{
	std::vector<Lit> literals;
};

struct InnerEquivalence{
	Lit	head;
	std::vector<Lit> literals;
	bool conjunctive;
};

struct InnerRule{
	Var head;
	std::vector<Lit> body;
	bool conjunctive;
	int definitionID;
};

struct InnerWLSet{
	AggType type;
	int setID;
	std::vector<WL> wls;

	InnerWLSet(int setID, const std::vector<Lit>& literals, const std::vector<Weight>& weights)
			:type(CARD), setID(setID){
		for(uint i=0; i<literals.size(); ++i){
			wls.push_back(WL(literals[i], weights[i]));
		}
	}

	InnerWLSet(int setID, const std::vector<WL>& wls)
			:type(CARD), setID(setID), wls(wls){
	}

	const std::vector<WL>& getWL() const { return wls; }
};

struct InnerAggregate{
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
};

struct InnerReifAggregate{
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
	Var head;
	AggSem sem;
	int defID; //Only relevant if defined aggregate
};

struct InnerMinimizeOrderedList{
	std::vector<Lit> literals;
};

struct InnerMinimizeSubset{
	std::vector<Lit> literals;
};

struct InnerMinimizeVar{
	uint varID;
};

struct InnerMinimizeAgg{
	Var head;
	int setID;
	AggType type;
};

struct InnerForcedChoices{
	std::vector<Lit> forcedchoices;
};

struct InnerSymmetryLiterals{
	std::vector<std::vector<Lit> > literalgroups;
};

struct InnerSymmetry{
	//INVAR keys are unique
	std::map<Var, Var> symmetry;
};

struct InnerRigidAtoms{
	std::vector<Var> rigidatoms;
};

struct InnerSubTheory{
	int child;
	Lit head;
};

struct InnerIntVarEnum{
	uint varID;
	std::vector<Weight> values;
};

struct InnerIntVarRange{
	uint varID;
	Weight minvalue, maxvalue;
};

struct InnerCPBinaryRel{
	Var head;
	uint varID;
	EqType rel;
	Weight bound;
};

struct InnerCPBinaryRelVar{
	Var head;
	uint lhsvarID, rhsvarID;
	EqType rel;
};

struct InnerCPSumWeighted{
	Var head;
	std::vector<uint> varIDs;
	std::vector<Weight> weights;
	EqType rel;
	Weight bound;
};

struct InnerCPCount{
	std::vector<uint> varIDs;
	Weight eqbound;
	EqType rel;
	uint rhsvar;
};

struct InnerCPAllDiff{
	std::vector<uint> varIDs;
};

class InnerPropagation{
public:
	int decisionlevel;
	Lit propagation;
};

class InnerBacktrack{
public:
	int untillevel;

	InnerBacktrack(int untillevel): untillevel(untillevel){}
};

class InnerLazyClause{
public:
	LazyGroundingCommand* monitor;
	Lit residual;
	bool watchboth;
};

class GenWatch{
public:
	virtual ~GenWatch(){}
	virtual void propagate() = 0;
	virtual const Lit& getPropLit() const = 0; // FIXME document which literal is watched and what that means (becoming false or true?)
	virtual bool dynamic() const = 0;
};

}
#endif /* UTILS_H_ */
