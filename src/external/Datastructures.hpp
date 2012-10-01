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

typedef unsigned int uint;

namespace MinisatID {

class Remapper;

// Comparison operator
enum class EqType {
	EQ, NEQ, L, G, GEQ, LEQ
};

EqType invertEqType(EqType type);

// Aggregate specification operators
enum class AggType {
	SUM, PROD, MIN, MAX, CARD
};
// Type of aggregate concerned
enum class AggSign {
	UB, // THE BOUND IS AN UPPER BOUND
	LB // THE BOUND IS A LOWER BOUND
};
// Sign of the bound of the aggregate
enum class AggSem {
	COMP, DEF, OR
};
// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

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
	VarID variable;
	int value;
};

struct Model {
	std::vector<Lit> literalinterpretations;
	std::vector<VariableEqValue> variableassignments;
};

typedef std::vector<Lit> literallist;
#define DEFAULTCONSTRID 1
// FIXME should be a number NOT used by any other constraint!

class ConstraintVisitor;
class Space;
class OneShotFlatzinc;
class OneShotUnsatCoreExtraction;

// NOTE: possible optimization during compilation:
// 	replace ID with a class without fields which always return {} for getID()

struct TheoryID{
	uint id;

	TheoryID(uint id): id(id){}

	bool operator==(TheoryID other) const{
		return id==other.id;
	}
	bool operator!=(TheoryID other) const{
		return not(this->operator ==(other));
	}
	bool operator<(TheoryID other) const{
		return id<other.id;
	}
};
#define DEFAULTTHEORYID 1

class Constraint {
public:
	TheoryID theoryid;
	Constraint(): theoryid(DEFAULTTHEORYID){

	}
	virtual ~Constraint(){}

	// Returns the set of all boolean variables relevant to this constraints
	// This allows constraint-independent code to check the existence of those literals
	virtual std::vector<Atom> getAtoms() const = 0;

	virtual void accept(ConstraintVisitor* visitor) = 0;
	virtual void accept(Space* visitor) = 0;
};

class ID: public Constraint {
private:
	uint _id;
public:
	ID(uint id)
			: _id(id) {
	}

	virtual ~ID() {
	}

	uint getID() const {
		return _id;
	}
};

#define DATASTRUCTURE_DECLAREACCEPT \
		void accept(ConstraintVisitor* visitor);\
		void accept(Space* visitor);

class Disjunction: public ID {
public:
	std::vector<Lit> literals;

	Disjunction(uint id, const std::vector<Lit>& literals)
			: ID(id), literals(literals) {
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
	IMPLIES, EQUIVALENT
};

class Implication: public ID {
public:
	Lit head;
	ImplicationType type;
	std::vector<Lit> body;
	bool conjunction;

	Implication(uint id, const Lit& head, ImplicationType type, const std::vector<Lit>& body, bool conjunction)
			: ID(id), head(head), type(type), body(body), conjunction(conjunction) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms = { var(head) };
		for (auto i = body.cbegin(); i < body.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}

	std::vector<Disjunction> getEquivalentClauses() const;
};

class Rule: public ID {
public:
	Atom head;
	std::vector<Lit> body;
	bool conjunctive;
	int definitionID;

	Rule(uint id, Atom head, const std::vector<Lit>& body, bool conjunctive, int definitionID)
			: ID(id), head(head), body(body), conjunctive(conjunctive), definitionID(definitionID) {
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

class WLSet: public Constraint {
public:
	int setID;
	std::vector<WLtuple> wl;
	const std::vector<WLtuple>& getWL() const {
		return wl;
	}

	WLSet(int setID)
			: setID(setID) {
	}
	WLSet(int setID, const std::vector<WLtuple>& wl)
			: setID(setID), wl(wl) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	std::vector<Atom> getAtoms() const {
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
	Lit head;
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
	AggSem sem;
	int defID; //Only relevant if defined aggregate, otherwise the value does not matter

	Aggregate(uint id, const Lit& head, int setID, Weight bound, AggType type, AggSign sign, AggSem sem, int defID)
			: ID(id), head(head), setID(setID), bound(bound), type(type), sign(sign), sem(sem), defID(defID) {
		MAssert(sem!=AggSem::DEF || defID!=-1);
		MAssert(sem!=AggSem::DEF || isPositive(head));
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

class MinimizeOrderedList: public Constraint {
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

class MinimizeSubset: public Constraint {
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

class MinimizeVar: public Constraint {
public:
	uint priority;
	VarID varID;

	MinimizeVar(uint priority, VarID varID)
			: priority(priority), varID(varID) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

class MinimizeAgg: public Constraint {
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

struct BoolVar: public ID {
	Atom atom;

	DATASTRUCTURE_DECLAREACCEPT

	BoolVar(uint id, Atom atom)
			: ID(id), atom(atom) {
	}

	virtual std::vector<Atom> getAtoms() const {
		return {atom};
	}
};

struct IntVarRange: public ID {
	VarID varID;
	Weight minvalue, maxvalue;

	DATASTRUCTURE_DECLAREACCEPT

	IntVarRange(uint id, VarID varID, const Weight& minvalue, const Weight& maxvalue)
			: ID(id), varID(varID), minvalue(minvalue), maxvalue(maxvalue) {
	}

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct IntVarEnum: public ID {
	VarID varID;
	std::vector<Weight> values;

	IntVarEnum(uint id, VarID varID, const std::vector<Weight>& values)
			: ID(id), varID(varID), values(values) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct CPBinaryRel: public ID {
	Lit head;
	VarID varID;
	EqType rel;
	Weight bound;

	CPBinaryRel(uint id, const Lit& head, VarID varID, EqType rel, const Weight& bound)
			: ID(id), head(head), varID(varID), rel(rel), bound(bound) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

struct CPBinaryRelVar: public ID {
	Lit head;
	VarID lhsvarID, rhsvarID;
	EqType rel;

	CPBinaryRelVar(uint id, const Lit& head, VarID lhsvarID, EqType rel, VarID rhsvarID)
			: ID(id), head(head), lhsvarID(lhsvarID), rhsvarID(rhsvarID), rel(rel) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

struct CPSumWeighted: public ID {
	Lit head;
	std::vector<VarID> varIDs;
	std::vector<Weight> weights;
	EqType rel;
	Weight bound;

	CPSumWeighted(uint id, const Lit& head, const std::vector<VarID>& varIDs, const std::vector<Weight>& weights, EqType rel, Weight bound)
			: ID(id), head(head), varIDs(varIDs), weights(weights), rel(rel), bound(bound) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

struct CPProdWeighted: public ID {
	Lit head;
	std::vector<VarID> varIDs;
	Weight prodWeight;
	EqType rel;
	VarID boundID;

	CPProdWeighted(uint id, const Lit& head, const std::vector<VarID>& varIDs, Weight prodweight, EqType rel, VarID boundid)
		: ID(id), head(head), varIDs(varIDs), prodWeight(prodweight), rel(rel), boundID(boundid) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

// Encodes: (number of varIDS equal to eqbound) rel rhsvar
struct CPCount: public ID {
	std::vector<VarID> varIDs;
	Weight eqbound;
	EqType rel;
	VarID rhsvar;

	CPCount(uint id, const std::vector<VarID>& varIDs, const Weight& eqbound, EqType rel, VarID rhsvar)
			: ID(id), varIDs(varIDs), eqbound(eqbound), rel(rel), rhsvar(rhsvar) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct CPAllDiff: public ID {
	std::vector<VarID> varIDs;

	CPAllDiff(uint id, const std::vector<VarID>& varIDs)
			: ID(id), varIDs(varIDs) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct CPElement: public ID {
	std::vector<VarID> varIDs;
	VarID index;
	VarID rhs;

	CPElement(uint id, const std::vector<VarID>& varids, VarID index, VarID rhs)
			: ID(id), varIDs(varids), index(index), rhs(rhs) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

class Symmetry: public Constraint {
public:
	// INVAR: the keys are unique
	std::vector<std::vector<Lit> > symmetry;
	Symmetry(std::vector<std::vector<Lit> > s)
			: symmetry(s) {
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

// POCO
class LazyGrounder {
public:
	LazyGrounder() {
	}
	virtual ~LazyGrounder() {
	}

	virtual void requestGrounding(int id, bool groundall, bool& stilldelayed) = 0;
};
class LazyGroundImpl: public ID {
public:
	Implication impl;
	LazyGrounder* monitor;

	LazyGroundImpl(uint id, const Implication& impl, LazyGrounder* monitor)
			: ID(id), impl(impl), monitor(monitor) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = impl.body.cbegin(); i < impl.body.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		atoms.push_back(var(impl.head));
		return atoms;
	}
};
class LazyAddition: public Constraint {
public:
	litlist list;
	int ref;

	LazyAddition(const litlist& list, int ref)
			: list(list), ref(ref) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for (auto i = list.cbegin(); i < list.cend(); ++i) {
			atoms.push_back(var(*i));
		}
		return atoms;
	}
};

enum class Value {
	True, False, Unknown
};

std::ostream& operator<<(std::ostream&, Value);

class LazyGroundingCommand {
private:
	bool allreadyground;
public:
	LazyGroundingCommand()
			: allreadyground(false) {
	}
	virtual ~LazyGroundingCommand() {
	}

	virtual void requestGrounding(Value currentValue) = 0;

	void notifyGrounded() {
		allreadyground = true;
	}
	bool isAlreadyGround() const {
		return allreadyground;
	}
};
class LazyGroundLit: public Constraint {
public:
	Value watchedvalue;
	Atom residual;
	LazyGroundingCommand* monitor;

	LazyGroundLit(Atom residual, Value watchedvalue, LazyGroundingCommand* monitor)
			: watchedvalue(watchedvalue), residual(residual), monitor(monitor) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {residual};
	}
};

struct TwoValuedRequirement: public Constraint {
	std::vector<Atom> atoms;

	TwoValuedRequirement(const std::vector<Atom>& atoms)
			: atoms(atoms) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return atoms;
	}
};

class SubTheory: public ID{
public:
	Atom head;
	TheoryID childid;
	std::vector<Atom> rigidatoms;

	SubTheory(uint id, Atom head, TheoryID childid, std::vector<Atom> atoms): ID(id), head(head), childid(childid), rigidatoms(atoms){}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return rigidatoms;
	}
 };

typedef std::vector<Model*> modellist;
typedef WLtuple WL;

}

#endif /* DATASTRUCTURES_HPP_ */
