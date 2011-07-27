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

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <map>
#include <string>

#include "satsolver/SATUtils.hpp"
#include "GeneralUtils.hpp"

typedef unsigned int uint;

namespace MinisatID {

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
	Var head;
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
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
};

}

#endif /* UTILS_H_ */
