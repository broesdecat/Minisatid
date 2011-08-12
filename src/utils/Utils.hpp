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
			EV_FULLASSIGNMENT, EV_ADDCLAUSE, EV_SYMMETRYANALYZE, EV_SYMMCHECK1, EV_SYMMCHECK2};

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
	vec<Lit> litassignments;
	std::vector<VariableEqValue> varassignments;
};

struct InnerDisjunction{
	vec<Lit> literals;

	InnerDisjunction(){}
	InnerDisjunction(const InnerDisjunction& orig){
		orig.literals.copyTo(literals);
	}

	void operator=(const InnerDisjunction& orig){
		orig.literals.copyTo(literals);
	}
};

struct InnerEquivalence{
	Lit	head;
	vec<Lit> literals;
	bool conjunctive;
};

struct InnerRule{
	Var head;
	vec<Lit> body;
	bool conjunctive;
	int definitionID;

	InnerRule(): head(-1), conjunctive(true), definitionID(-1){}
	InnerRule(const InnerRule& rule): head(rule.head), conjunctive(rule.conjunctive), definitionID(rule.definitionID){
		rule.body.copyTo(body);
	}
};

struct InnerSet{
	int setID;
	std::vector<Lit> literals;
};

struct InnerWSet{
	int setID;
	std::vector<Lit> literals;
	std::vector<Weight> weights;
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
	vec<Lit> literals;
};

struct InnerMinimizeSubset{
	vec<Lit> literals;
};

struct InnerMinimizeAgg{
	Var head;
	int setID;
	AggType type;
};

struct InnerForcedChoices{
	vec<Lit> forcedchoices;
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

}

#endif /* UTILS_H_ */
