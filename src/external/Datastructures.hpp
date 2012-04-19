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
#include <cstdint>
#include <cstdlib>
#include "Weight.hpp"
#include "Lit.hpp"
#include "MAssert.hpp"

namespace MinisatID {

class Remapper;

// Comparison operator
enum class EqType {
	EQ, NEQ, L, G, GEQ, LEQ
};

// Aggregate specification operators
enum class AggType {
	SUM, PROD, MIN, MAX, CARD
};
// Type of aggregate concerned
enum class AggSign {
	UB, LB
};
// Sign of the bound of the aggregate
enum class AggSem {
	COMP, DEF, OR
};
// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

typedef Lit Literal;
typedef Var Atom;

// A class representing a tuple of a literal and an associated weight
struct WLtuple {
	Lit l;
	Weight w;

	const Lit& getLit() const {
		return l;
	}
	const Weight& getWeight() const {
		return w;
	}

	WLtuple(const Lit& l, const Weight& w)
			: l(l), w(w) {
	}

	bool operator<(const WLtuple& p) const {
		return w < p.w;
	}
	bool operator<(const Weight& bound) const {
		return w < bound;
	}
	bool operator==(const WLtuple& p) const {
		return w == p.w && l == p.l;
	}
};

//Compare WLs by their literals, placing same literals next to each other
template<class Tuple>
bool compareWLByLits(const Tuple& one, const Tuple& two) {
	return var(one.getLit()) < var(two.getLit());
}

//Compare WLs by their weights
template<class T>
bool compareByWeights(const T& one, const T& two) {
	return one.getWeight() < two.getWeight();
}

template<class Tuple>
bool compareWLByAbsWeights(const Tuple& one, const Tuple& two) {
	return abs(one.getWeight()) < abs(two.getWeight());
}

struct VariableEqValue {
	int variable;
	int value;
};

struct Model {
	std::vector<Lit> literalinterpretations;
	std::vector<VariableEqValue> variableassignments;
};

typedef std::vector<Literal> literallist;

class ConstraintVisitor;
class Space;
class OneShotFlatzinc;
class OneShotUnsatCoreExtraction;

class ID {
private:
	static int nextid;
public:
	int id;
	ID()
			: id(nextid) {
		nextid++;
	}
	ID(int id)
			: id(id) { // FIXME add to interface!
	}
	virtual ~ID() {
	}

	virtual std::vector<Atom> getAtoms() const = 0;
	virtual void accept(ConstraintVisitor* visitor) = 0;
	virtual void accept(Space* visitor) = 0;
};

#define DATASTRUCTURE_DECLAREACCEPT \
void accept(ConstraintVisitor* visitor);\
void accept(Space* visitor);

class Disjunction: public ID {
public:
	std::vector<Lit> literals;
	Disjunction() {
	}
	Disjunction(const std::vector<Lit>& literals)
			: literals(literals) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}
};

enum class ImplicationType {
	IMPLIES, IMPLIEDBY, EQUIVALENT
};

class Implication: public ID {
public:
	const Lit head;
	const ImplicationType type;
	const std::vector<Lit> body;
	const bool conjunction;

	Implication(const Lit& head, ImplicationType type, const std::vector<Lit>& body, bool conjunction)
			: head(head), type(type), body(body), conjunction(conjunction) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms = { var(head) };
		for (auto i = body.cbegin(); i < body.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}
};

class Rule: public ID {
public:
	Var head;
	std::vector<Lit> body;
	bool conjunctive;
	int definitionID;

	Rule()
			: head(0) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms = { head };
		for (auto i = body.cbegin(); i < body.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}
};

class WLSet: public ID {
public:
	int setID;
	std::vector<WLtuple> wl;
	const std::vector<WLtuple>& getWL() const {
		return wl;
	}

	WLSet(int setID): setID(setID){
	}
	WLSet(int setID, const std::vector<WLtuple>& wl): setID(setID), wl(wl){

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = wl.cbegin(); i < wl.cend(); ++i) {
			atoms.push_back(var(i->getLit()));
		}
		return atoms;
	}
};

WLSet createSet(int setid, const std::vector<Lit>& literals, const Weight& w);
WLSet createSet(int setid, const std::vector<Lit>& literals, const std::vector<Weight>& weights);

class Aggregate: public ID {
public:
	Var head;
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
	AggSem sem;
	int defID; //Only relevant if defined aggregate

	Aggregate(Var head, int setID, Weight bound, AggType type, AggSign sign, AggSem sem, int defID)
			: head(head), setID(setID), bound(bound), type(type), sign(sign), sem(sem), defID(defID) {
		MAssert(sem!=AggSem::DEF || defID!=-1);
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {head};
	}
};

class MinimizeOrderedList: public ID {
public:
	uint priority;
	std::vector<Lit> literals;

	MinimizeOrderedList(uint priority, std::vector<Lit> literals)
			: priority(priority), literals(literals) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}
};

class MinimizeSubset: public ID {
public:
	uint priority;
	std::vector<Lit> literals;

	MinimizeSubset(uint priority, std::vector<Lit> literals)
			: priority(priority), literals(literals) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}
};

class MinimizeVar: public ID {
public:
	uint priority;
	uint varID;

	MinimizeVar(uint priority, uint varID)
			: priority(priority), varID(varID) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

class MinimizeAgg: public ID {
public:
	uint priority;
	int setid;
	AggType type;

	MinimizeAgg(uint priority, int setid, AggType type)
			: priority(priority), setid(setid), type(type) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct IntVarRange: public ID {
	uint varID;
	Weight minvalue, maxvalue;

	DATASTRUCTURE_DECLAREACCEPT

	IntVarRange(uint varID, const Weight& minvalue, const Weight& maxvalue)
			: varID(varID), minvalue(minvalue), maxvalue(maxvalue) {

	}

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct IntVarEnum: public ID {
	uint varID;
	std::vector<Weight> values;

	IntVarEnum(uint varID, const std::vector<Weight>& values)
			: varID(varID), values(values) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct CPBinaryRel: public ID {
	Var head;
	uint varID;
	EqType rel;
	Weight bound;

	CPBinaryRel(Var head, uint varID, EqType rel, const Weight& bound)
			: head(head), varID(varID), rel(rel), bound(bound) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {head};
	}
};

struct CPBinaryRelVar: public ID {
	Var head;
	uint lhsvarID, rhsvarID;
	EqType rel;

	CPBinaryRelVar(Var head, uint lhsvarID, EqType rel, uint rhsvarID)
			: head(head), lhsvarID(lhsvarID), rhsvarID(rhsvarID), rel(rel) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {head};
	}
};

struct CPSumWeighted: public ID {
	Var head;
	std::vector<uint> varIDs;
	std::vector<Weight> weights;
	EqType rel;
	Weight bound;

	CPSumWeighted(Var head, const std::vector<uint>& varIDs, const std::vector<Weight>& weights, EqType rel, Weight bound)
			: head(head), varIDs(varIDs), weights(weights), rel(rel), bound(bound) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {head};
	}
};

struct CPCount: public ID {
	std::vector<uint> varIDs;
	Weight eqbound;
	EqType rel;
	uint rhsvar;

	CPCount(const std::vector<uint>& varIDs, const Weight& eqbound, EqType rel, uint rhsvar)
			: varIDs(varIDs), eqbound(eqbound), rel(rel), rhsvar(rhsvar) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct CPAllDiff: public ID {
	std::vector<uint> varIDs;

	CPAllDiff(const std::vector<uint>& ids)
			: varIDs(ids) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct CPElement: public ID {
	std::vector<uint> varIDs;
	uint index;
	uint rhs;

	CPElement(const std::vector<uint>& ids, uint index, uint rhs)
			: varIDs(ids), index(index), rhs(rhs) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

class Symmetry: public ID {
public:
	// INVAR: the keys are unique
	std::vector<std::vector<Literal> > symmetry;
	Symmetry(std::vector<std::vector<Literal> > s) : symmetry(s){

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = symmetry.cbegin(); i < symmetry.cend(); ++i) {
			for (auto j = i->cbegin(); j < i->cend(); ++j) {
				atoms.push_back(var(*j));
			}
		}
		return atoms;
	}
};

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
class LazyGroundLit: public ID {
public:
	bool watchboth;
	Lit residual;
	LazyGroundingCommand* monitor;

	LazyGroundLit(bool watchboth, const Lit& residual, LazyGroundingCommand* monitor)
			: watchboth(watchboth), residual(residual), monitor(monitor) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(residual)};
	}
};

typedef std::vector<Model*> modellist;
typedef WLtuple WL;

}

#endif /* DATASTRUCTURES_HPP_ */
