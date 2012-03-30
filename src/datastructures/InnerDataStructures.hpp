/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef INNERDATASTRUCTURES_HPP_
#define INNERDATASTRUCTURES_HPP_

#include <vector>

#include "utils/Utils.hpp"
#include "WL.hpp"

namespace MinisatID{

struct InnerModel{
	std::vector<Lit> litassignments;
	std::vector<VariableEqValue> varassignments;
};

struct InnerDisjunction{
	std::vector<Lit> literals;
};

struct InnerImplication{
	Lit	head;
	ImplicationType type;
	std::vector<Lit> literals;
	bool conjunctive;

	InnerImplication(){}
	InnerImplication(const Lit& head, ImplicationType type, const std::vector<Lit>& literals, bool conjunctive):
		head(head), type(type), literals(literals), conjunctive(conjunctive){

	}
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
			:type(AggType::CARD), setID(setID){
		for(uint i=0; i<literals.size(); ++i){
			wls.push_back(WL(literals[i], weights[i]));
		}
	}

	InnerWLSet(int setID, const std::vector<WL>& wls)
			:type(AggType::CARD), setID(setID), wls(wls){
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
	int setID;
	AggType type;
};

struct InnerForcedChoices{
	std::vector<Lit> forcedchoices;
};

struct InnerSymmetry{
	//INVAR keys are unique
	std::map<Lit, Lit> symmetry;
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
	virtual const Lit& getPropLit() const = 0;
	virtual bool dynamic() const = 0;
};

}
#endif /* INNERDATASTRUCTURES_HPP_ */
