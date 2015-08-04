/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <vector>
#include <map>
#include <unordered_map>
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
	EQ,
	NEQ,
	L,
	G,
	GEQ,
	LEQ
};

EqType invertEqType(EqType type);

// Aggregate specification operators
enum class AggType {
	SUM,
	PROD,
	MIN,
	MAX,
	CARD
};
// Type of aggregate concerned
enum class AggSign {
	UB, // THE BOUND IS AN UPPER BOUND
	LB // THE BOUND IS A LOWER BOUND
};
// Sign of the bound of the aggregate
enum class AggSem {
	COMP,
	DEF,
	OR
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
			: 	l(l),
				w(w) {
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
private:
	VarID variable;
	int value;
	bool hasimage;

public:
	VariableEqValue(VarID variable, int value, bool noImage)
			: 	variable(variable),
				value(value),
				hasimage(noImage) {

	}

	bool hasValue() const {
		return hasimage;
	}
	int getValue() const {
		MAssert(hasValue());
		return value;
	}
	VarID getVariable() const {
		return variable;
	}
};

struct Model {
	std::vector<Lit> literalinterpretations;
	std::vector<VariableEqValue> variableassignments;
};

typedef std::vector<Lit> literallist;

class ConstraintVisitor;
class Space;

// NOTE: possible optimization during compilation:
// 	replace ID with a class without fields which always return {} for getID()

struct TheoryID {
	uint id;

	TheoryID(uint id)
			: id(id) {
	}

	bool operator==(TheoryID other) const {
		return id == other.id;
	}
	bool operator!=(TheoryID other) const {
		return not (this->operator ==(other));
	}
	bool operator<(TheoryID other) const {
		return id < other.id;
	}
};
#define DEFAULTTHEORYID 1

class Constraint {
public:
	TheoryID theoryid;
	Constraint()
			: theoryid(DEFAULTTHEORYID) {

	}
	virtual ~Constraint() {
	}

	// Returns the set of all boolean variables relevant to this constraints
	// This allows constraint-independent code to check the existence of those literals
	virtual std::vector<Atom> getAtoms() const = 0;

	virtual void accept(ConstraintVisitor* ) = 0;
	virtual void accept(Space* visitor) = 0;
};

#define DATASTRUCTURE_DECLAREACCEPT \
		void accept(ConstraintVisitor* visitor);\
		void accept(Space* visitor);

class Disjunction: public Constraint {
public:
	std::vector<Lit> literals;

	Disjunction(const std::vector<Lit>& literals)
			:
				literals(literals) {
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
	IMPLIES,
	IMPLIEDBY,
	EQUIVALENT
};

class Implication: public Constraint {
public:
	Lit head;
	ImplicationType type;
	std::vector<Lit> body;
	bool conjunction;

	Implication(const Lit& head, ImplicationType type, const std::vector<Lit>& body, bool conjunction)
			:
				head(head),
				type(type),
				body(body),
				conjunction(conjunction) {
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

/**
 * A definition can be seen as
 * 		- if part of completion (body implies head)
 * 		- only-if part of completion (head implies body)
 * 		- unfounded set constraint
 *
 * By default the Rule and (defined) Aggregate datastructures imply all three of those.
 * Sometimes it is useful to represent the only-if and ufs together while the if part is added separately (as clauses),
 * namely because the only-if and ufs watch heads not being true, whlie the if watches heads not being false.
 * The "onlyif" option means that they only constrain to no unfounded sets and the only-if of the completion
 */
class Rule: public Constraint {
public:
	Atom head;
	std::vector<Lit> body;
	bool conjunctive;
	int definitionID;
	bool onlyif;

	Rule(Atom head, const std::vector<Lit>& body, bool conjunctive, int definitionID, bool onlyif)
			:
				head(head),
				body(body),
				conjunctive(conjunctive),
				definitionID(definitionID),
				onlyif(onlyif) {
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
			: 	setID(setID),
				wl(wl) {
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

class Aggregate: public Constraint {
public:
	Lit head;
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
	AggSem sem;
	int defID; //Only relevant if defined aggregate, otherwise the value does not matter
	bool onlyif;

	Aggregate(const Lit& head, int setID, Weight bound, AggType type, AggSign sign, AggSem sem, int defID, bool onlyif)
			:
				head(head),
				setID(setID),
				bound(bound),
				type(type),
				sign(sign),
				sem(sem),
				defID(defID),
				onlyif(onlyif) {
		MAssert(sem!=AggSem::DEF || defID!=-1);
		MAssert(sem!=AggSem::DEF || isPositive(head));
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

class MinimizeSubset: public Constraint {
public:
	uint priority;
	std::vector<Lit> literals;

	MinimizeSubset(uint priority, std::vector<Lit> literals)
			: 	priority(priority),
				literals(literals) {
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

class OptimizeVar: public Constraint {
public:
	uint priority;
	VarID varID;
	bool minimize; // false = maximize

	OptimizeVar(uint priority, VarID varID, bool minimize)
			: 	priority(priority),
				varID(varID),
				minimize(minimize) {
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
			: 	priority(priority),
				setid(setid),
				type(type) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}
};

struct BoolVar: public Constraint {
	Atom atom;

	DATASTRUCTURE_DECLAREACCEPT

	BoolVar(Atom atom)
			:
				atom(atom) {
	}

	virtual std::vector<Atom> getAtoms() const {
		return {atom};
	}
};

struct IntVarRange: public Constraint {
	bool partial;
	Lit possiblynondenoting; // Should not be used if partial is false
	VarID varID;
	Weight minvalue, maxvalue;

	DATASTRUCTURE_DECLAREACCEPT

#ifndef NOARBITPREC
	IntVarRange(VarID varID)
			:
				partial(false),
				possiblynondenoting(mkNegLit(1)),
				varID(varID),
				minvalue(Weight(false)),
				maxvalue(Weight(true)) {
	}
#endif

	IntVarRange(VarID varID, const Weight& minvalue, const Weight& maxvalue)
			:
			  	partial(false),
			  	possiblynondenoting(mkNegLit(1)),
				varID(varID),
				minvalue(minvalue),
				maxvalue(maxvalue) {
	}
	IntVarRange(VarID varID, const Weight& minvalue, const Weight& maxvalue, Lit possiblynondenoting)
			:
			  	partial(true),
			  	possiblynondenoting(possiblynondenoting),
				varID(varID),
				minvalue(minvalue),
				maxvalue(maxvalue) {
	}

	virtual std::vector<Atom> getAtoms() const {
		if(partial){
			return {possiblynondenoting.getAtom()};
		}else{
			return {};
		}
	}
};

struct IntVarEnum: public Constraint {
	bool partial;
	Lit possiblynondenoting; // Should not be used if partial is false
	VarID varID;
	std::vector<Weight> values;

	IntVarEnum(VarID varID, const std::vector<Weight>& values)
			:
			  	partial(false),
			  	possiblynondenoting(mkPosLit(1)),
				varID(varID),
				values(values) {
	}
	IntVarEnum(VarID varID, const std::vector<Weight>& values, Lit possiblynondenoting)
			:
			  	partial(true),
			  	possiblynondenoting(possiblynondenoting),
				varID(varID),
				values(values) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		if(partial){
			return {possiblynondenoting.getAtom()};
		}else{
			return {};
		}
	}
};

struct CPBinaryRel: public Constraint {
	Lit head;
	VarID varID;
	EqType rel;
	Weight bound;

	CPBinaryRel(const Lit& head, VarID varID, EqType rel, const Weight& bound)
			:
				head(head),
				varID(varID),
				rel(rel),
				bound(bound) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

struct CPBinaryRelVar: public Constraint {
	Lit head;
	VarID lhsvarID, rhsvarID;
	EqType rel;

	CPBinaryRelVar(const Lit& head, VarID lhsvarID, EqType rel, VarID rhsvarID)
			:
				head(head),
				lhsvarID(lhsvarID),
				rhsvarID(rhsvarID),
				rel(rel) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {var(head)};
	}
};

struct CPSumWeighted: public Constraint {
	Lit head;
	std::vector<Lit> conditions;
	std::vector<VarID> varIDs;
	std::vector<Weight> weights;
	EqType rel;
	Weight bound;

	CPSumWeighted(const Lit& head, const std::vector<Lit>& conditions, const std::vector<VarID>& varIDs, const std::vector<Weight>& weights,
			EqType rel, Weight bound)
			:
				head(head),
				conditions(conditions),
				varIDs(varIDs),
				weights(weights),
				rel(rel),
				bound(bound) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for(auto lit: conditions){
			atoms.push_back(var(lit));
		}
		atoms.push_back(var(head));
		return atoms;
	}
};

struct CPProdWeighted: public Constraint {
	Lit head;
	std::vector<Lit> conditions;
	std::vector<VarID> varIDs;
	Weight prodWeight;
	EqType rel;
	VarID boundID;

	CPProdWeighted(const Lit& head, const std::vector<Lit>& conditions, const std::vector<VarID>& varIDs, Weight prodweight, EqType rel, VarID boundid)
			:
				head(head),
				conditions(conditions),
				varIDs(varIDs),
				prodWeight(prodweight),
				rel(rel),
				boundID(boundid) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		std::vector<Atom> atoms;
		for(auto lit: conditions){
			atoms.push_back(var(lit));
		}
		atoms.push_back(var(head));
		return atoms;
	}
};

struct CPAllDiff: public Constraint {
	std::vector<VarID> varIDs;

	CPAllDiff(const std::vector<VarID>& varIDs)
			:
				varIDs(varIDs) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
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
class LazyGroundImpl: public Constraint {
public:
	Implication impl;
	LazyGrounder* monitor;

	LazyGroundImpl(const Implication& impl, LazyGrounder* monitor)
			:
				impl(impl),
				monitor(monitor) {
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
			: 	list(list),
				ref(ref) {
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
	True,
	False,
	Unknown
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
			: 	watchedvalue(watchedvalue),
				residual(residual),
				monitor(monitor) {
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

struct TwoValuedVarIdRequirement: public Constraint {
	VarID vid;

	TwoValuedVarIdRequirement(VarID vid)
			: vid(vid) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {};
	}

	virtual ~TwoValuedVarIdRequirement() {}

};

class SubTheory: public Constraint {
public:
	Atom head;
	TheoryID childid;
	std::vector<Atom> rigidatoms;

	SubTheory(Atom head, TheoryID childid, std::vector<Atom> atoms)
			:
				head(head),
				childid(childid),
				rigidatoms(atoms) {
	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return rigidatoms;
	}
};

/**
 * Responsible for lazily grounding P <=> Q(c1, ..., cn) when P and c1, ..., cn are known.
 */
class LazyAtomGrounder {
public:
	virtual ~LazyAtomGrounder() {
	}

	virtual bool isFunction() const = 0;
	virtual std::string getSymbolName() const = 0;

	/**
	 * Given the constraint P <=> Q(t1, ..., tn) with all t integer variables.
	 * Given a value for P/0 and for all arguments (except the last one if Q/n is a function,
	 * adds the constraint
	 * 	  if P/0 is true and Q/n is not a function
	 *  		P & t1=v1 & ... & tn=vn => Q(v1, ..., vn)
	 * 	  if P/0 is true and Q/n is a function
	 *  		P & t1=v1 & ... & tn-1=vn-1 => Q(v1, ..., vn-1)=vn
	 * 	  if P/0 is false and Q/n is not a function
	 *  		~P & t1=v1 & ... & tn=vn => ~Q(v1, ..., vn)
	 * 	  if P/0 is false and Q/n is a function
	 *  		analogously
	 */
	virtual void ground(bool headvalue, const std::vector<int>& argvalues) = 0;
};

/*
 * Represents a constraint of the form head <=> P(args), where args is a set of cp variables and P is lazily grounded by the passed-in grounder.
 */
class LazyAtom: public Constraint {
public:
	Lit head;
	std::vector<VarID> args;
	LazyAtomGrounder* grounder;

	LazyAtom(const Lit& head, const std::vector<VarID>& args, LazyAtomGrounder* grounder)
			:
				head(head),
				args(args),
				grounder(grounder) {

	}

	DATASTRUCTURE_DECLAREACCEPT

	virtual std::vector<Atom> getAtoms() const {
		return {head.getAtom()};
	}
};

typedef std::vector<Model*> modellist;
typedef WLtuple WL;

}
