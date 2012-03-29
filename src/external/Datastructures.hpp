/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef DATASTRUCTURES_HPP_
#define DATASTRUCTURES_HPP_

#include <vector>
#include <map>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include "Weight.hpp"
#include "MAssert.hpp"

namespace MinisatID {

enum class Optim {
	LIST, SUBSET, AGG, NONE
};

// Comparison operator
enum class EqType	{ EQ, NEQ, L, G, GEQ, LEQ };

// Aggregate specification operators
enum class AggType 	{ SUM, PROD, MIN, MAX, CARD }; 	// Type of aggregate concerned
enum class AggSign 	{ UB, LB}; 	// Sign of the bound of the aggregate
enum class AggSem 	{ COMP, DEF, IMPLICATION };	// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

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
	explicit Literal(int a, bool s = false): lit(s?-a:a){ MAssert(a>=0); }
	explicit Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){ MAssert(a.getValue()>=0); }

	int		getValue()						const { return lit; }
	Atom 	getAtom() 						const { return Atom(lit<0?-lit:lit); }
	bool 	hasSign() 						const { return lit<0; }
	bool 	operator== (const Literal& l) 	const { return lit == l.lit; }
	bool 	operator< (const Literal& l) 	const {	return std::abs(lit) < std::abs(l.lit); }
	Literal operator~()						const { return Literal(getAtom(), lit>0?true:false); }
	Literal operator!()						const { return Literal(getAtom(), lit>0?true:false); }
};

std::string printLiteral(const Literal& lit);

// A class representing a tuple of a literal and an associated weight
struct WLtuple{
	const Literal l;
	const Weight w;

	WLtuple(const Literal& l, const Weight& w): l(l), w(w){ }
	WLtuple operator=(const WLtuple& lw) const { return WLtuple(lw.l, lw.w); }
};

typedef std::vector<Literal> literallist;

struct VariableEqValue{
	int variable;
	int value;
};

struct Model{
	std::vector<Literal> literalinterpretations;
	std::vector<VariableEqValue> variableassignments;
};

typedef std::vector<Model*> modellist;

class Disjunction{
public:
	std::vector<Literal> literals;
};

enum class ImplicationType { IMPLIES, IMPLIEDBY, EQUIVALENT};
class Implication{
public:
	const Literal	head;
	const ImplicationType type;
	const literallist body;
	const bool conjunction;

	Implication(const Literal& head, ImplicationType type, const literallist& body, bool conjunction):
		head(head), type(type), body(body), conjunction(conjunction){

	}
};

class Rule{
public:
	Atom head;
	literallist body;
	bool conjunctive;
	int definitionID;

	Rule(): head(0){}
};

class Set{
public:
	int setID;
	literallist literals;
};

class WSet{
public:
	int setID;
	literallist literals;
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
	literallist literals;
};

class MinimizeSubset{
public:
	literallist literals;
};

class MinimizeVar{
public:
	uint varID;
};

class MinimizeAgg{
public:
	int setid;
	AggType type;
};

struct CPIntVarRange{
	uint varID;
	Weight minvalue, maxvalue;
};

struct CPIntVarEnum{
	uint varID;
	std::vector<Weight> values;
};

struct CPBinaryRel{
	Atom head;
	uint varID;
	EqType rel;
	Weight bound;

	CPBinaryRel(): head(0){}
};

struct CPBinaryRelVar{
	Atom head;
	uint lhsvarID, rhsvarID;
	EqType rel;

	CPBinaryRelVar(): head(0){}
};

struct CPSumWeighted{
	Atom head;
	std::vector<uint> varIDs;
	std::vector<Weight> weights;
	EqType rel;
	Weight bound;

	CPSumWeighted(): head(0){}
};

struct CPCount{
	std::vector<uint> varIDs;
	Weight eqbound;
	EqType rel;
	uint rhsvar;
};

struct CPAllDiff{
	std::vector<uint> varIDs;
};

class ForcedChoices{
public:
	literallist forcedchoices;
};

class Symmetry{
public:
	// INVAR: the keys are unique
	std::map<Literal, Literal> symmetry;
};

// FIXME add callback again?
class LazyGroundingCommand {
private:
	bool allreadyground;
public:
	LazyGroundingCommand()
			: allreadyground(false) {
	}
	virtual ~LazyGroundingCommand() {
	}

	virtual void requestGrounding() = 0;

	void notifyGrounded() {
		allreadyground = true;
	}
	bool isAlreadyGround() const {
		return allreadyground;
	}
};

// POCO
class LazyGroundLit {
public:
	bool watchboth;
	Literal residual;
	LazyGroundingCommand* monitor;

	LazyGroundLit(bool watchboth, const Literal& residual, LazyGroundingCommand* monitor)
			: watchboth(watchboth), residual(residual), monitor(monitor) {
	}
};

}

#endif /* DATASTRUCTURES_HPP_ */
