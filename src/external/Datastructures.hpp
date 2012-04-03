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
#include "MAssert.hpp"
#include "satsolver/BasicSATUtils.hpp"

namespace MinisatID {

class Remapper;

enum class Optim {
	LIST, SUBSET, AGG, NONE
};

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
	COMP, DEF, IMPLICATION
};
// Semantics of satisfiability of the aggregate head: COMPletion or DEFinitional

class Atom {
private:
	int atom; //Important: because of mutual exclusion of const members and a clean assignment operator, i did not make this constant, but semantically it should be

public:
	explicit Atom(int a) :
			atom(a) {
	}
	int getValue() const {
		return atom;
	}

	bool operator==(const Atom& a) const {
		return atom == a.atom;
	}
	bool operator<(const Atom& a) const {
		return atom < a.atom;
	}
};

class Literal {
private:
	int lit;

public:
	//@pre: a is positive
	explicit Literal(int a, bool s = false) :
			lit(s ? -a : a) {
		MAssert(a>=0);
	}
	explicit Literal(Atom a, bool s = false) :
			lit(s ? -a.getValue() : a.getValue()) {
		MAssert(a.getValue()>=0);
	}

	int getValue() const {
		return lit;
	}
	Atom getAtom() const {
		return Atom(lit < 0 ? -lit : lit);
	}
	bool hasSign() const {
		return lit < 0;
	}
	bool operator==(const Literal& l) const {
		return lit == l.lit;
	}
	bool operator<(const Literal& l) const {
		return std::abs(lit) < std::abs(l.lit);
	}
	Literal operator~() const {
		return Literal(getAtom(), lit > 0 ? true : false);
	}
	Literal operator!() const {
		return Literal(getAtom(), lit > 0 ? true : false);
	}
};

std::string printLiteral(const Literal& lit);

// A class representing a tuple of a literal and an associated weight
template<class L>
struct WLtuple {
	const L l;
	const Weight w;

	const L& getLit() const {
		return l;
	}
	const Weight& getWeight() const {
		return w;
	}

	WLtuple(const L& l, const Weight& w) :
			l(l), w(w) {
	}
	WLtuple<L> operator=(const WLtuple<L>& lw) const {
		return WLtuple(lw.l, lw.w);
	}

	bool operator<(const WLtuple<L>& p) const {
		return w < p.w;
	}
	bool operator<(const Weight& bound) const {
		return w < bound;
	}
	bool operator==(const WLtuple<L>& p) const {
		return w == p.w && l == p.l;
	}
};

Var atom(const Lit& lit);
Atom atom(const Literal& lit);

//Compare WLs by their literals, placing same literals next to each other
template<typename L>
bool compareWLByLits(const WLtuple<L>& one, const WLtuple<L>& two){
	return atom(one.getLit()) < atom(two.getLit());
}

//Compare WLs by their weights
template<class T>
bool compareByWeights(const T& one, const T& two) {
	return one.getWeight() < two.getWeight();
}

template<typename L>
bool compareWLByAbsWeights(const WLtuple<L>& one, const WLtuple<L>& two){
	return abs(one.getWeight()) < abs(two.getWeight());
}

struct VariableEqValue {
	int variable;
	int value;
};

template<class L>
struct M {
	std::vector<L> literalinterpretations;
	std::vector<VariableEqValue> variableassignments;
};

typedef std::vector<Literal> literallist;

class ID {
public:
	const int id;
	ID(int id) :
			id(id) {

	}
	ID(const ID& id) :
			id(id.id) {

	}
};

template<class L>
class Disj {
public:
	std::vector<L> literals;
	Disj(){}
	Disj(const std::vector<L>& literals): literals(literals){}
};

enum class ImplicationType {
	IMPLIES, IMPLIEDBY, EQUIVALENT
};
template<class L>
class Impl {
public:
	const L head;
	const ImplicationType type;
	const std::vector<L> body;
	const bool conjunction;

	Impl(const L& head, ImplicationType type, const std::vector<L>& body, bool conjunction) :
			head(head), type(type), body(body), conjunction(conjunction) {

	}
};

template<class A, class L>
class R {
public:
	A head;
	std::vector<L> body;
	bool conjunctive;
	int definitionID;

	R() :
			head(0) {
	}
};

template<class L>
class S {
public:
	int setID;
	std::vector<L> literals;
};

template<class L>
class WS {
public:
	int setID;
	std::vector<L> literals;
	std::vector<Weight> weights;
};

template<class L>
class WLS {
public:
	int setID;
	std::vector<WLtuple<L> > wl;
	const std::vector<WLtuple<L> >& getWL() const {
		return wl;
	}
};

template<class A>
class AggD {
public:
	A head;
	int setID;
	Weight bound;
	AggType type;
	AggSign sign;
	AggSem sem;
	int defID; //Only relevant if defined aggregate

	AggD() :
			head(0) {
	}
};

template<class L>
class MnmOrderedList {
public:
	std::vector<L> literals;
};

template<class L>
class MnmSubset {
public:
	std::vector<L> literals;
};

class MnmVar {
public:
	uint varID;
};

class MnmAgg {
public:
	int setid;
	AggType type;
};

struct IntVarRange {
	uint varID;
	Weight minvalue, maxvalue;
};

struct IntVarEnum {
	uint varID;
	std::vector<Weight> values;
};

template<class A>
struct BinaryRel {
	A head;
	uint varID;
	EqType rel;
	Weight bound;

	BinaryRel() :
			head(0) {
	}
};

template<class A>
struct BinaryRelVar {
	A head;
	uint lhsvarID, rhsvarID;
	EqType rel;

	BinaryRelVar() :
			head(0) {
	}
};

template<class A>
struct SumWeighted {
	A head;
	std::vector<uint> varIDs;
	std::vector<Weight> weights;
	EqType rel;
	Weight bound;

	SumWeighted() :
			head(0) {
	}
};

struct Count {
	std::vector<uint> varIDs;
	Weight eqbound;
	EqType rel;
	uint rhsvar;
};

struct AllDiff {
	std::vector<uint> varIDs;

	AllDiff(const std::vector<uint>& ids) :
			varIDs(ids) {
	}
	AllDiff convert(const AllDiff& orig, Remapper*) {
		return AllDiff(orig);
	}
};

template<class LFrom>
struct Convert;

template<>
struct Convert<Literal> {
	typedef Lit LTo;
};

template<>
struct Convert<Lit> {
	typedef Literal LTo;
};

template<class T, class T2>
T2 get(const T&, Remapper* remapper);

template<class L>
class Sym {
public:
	// INVAR: the keys are unique
	std::map<L, L> symmetry;

	Sym() {
	}
	Sym(const std::map<L, L>& symmetry) :
			symmetry(symmetry) {
	}
	Sym<typename Convert<L>::LTo> convert(Remapper* remapper) {
		std::map<typename Convert<L>::LTo, typename Convert<L>::LTo> newmap;
		for (auto i = symmetry.cbegin(); i < symmetry.cend(); ++i) {
			newmap.insert(get(i->first, remapper), get(i->second, remapper));
		}
		return Sym(newmap);
	}
};

// FIXME add callback again?
class LazyGroundingCommand {
private:
	bool allreadyground;
public:
	LazyGroundingCommand() :
			allreadyground(false) {
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
template<class L>
class LazyLit {
public:
	bool watchboth;
	L residual;
	LazyGroundingCommand* monitor;

	LazyLit(bool watchboth, const L& residual, LazyGroundingCommand* monitor) :
			watchboth(watchboth), residual(residual), monitor(monitor) {
	}
};

typedef Sym<Literal> Symmetry;
typedef Sym<Lit> InnerSymmetry;
typedef Disj<Literal> Disjunction;
typedef Disj<Lit> InnerDisjunction;
typedef R<Atom, Literal> Rule;
typedef R<int, Lit> InnerRule;
typedef S<Literal> Set;
typedef S<Lit> InnerSet;
typedef WS<Literal> WSet;
typedef WS<Lit> InnerWSet;
typedef WLS<Literal> WLSet;
typedef WLS<Lit> InnerWLSet;
typedef Impl<Literal> Implication;
typedef Impl<Lit> InnerImplication;
typedef AggD<Atom> Aggregate;
typedef AggD<int> InnerReifAggregate;
typedef LazyLit<Literal> LazyGroundLit;
typedef LazyLit<Lit> InnerLazyGroundLit;
typedef MnmOrderedList<Literal> MinimizeOrderedList;
typedef MnmOrderedList<Lit> InnerMinimizeOrderedList;
typedef MnmSubset<Literal> MinimizeSubset;
typedef MnmSubset<Lit> InnerMinimizeSubset;
typedef MnmVar MinimizeVar;
typedef MnmVar InnerMinimizeVar;
typedef MnmAgg MinimizeAgg;
typedef MnmAgg InnerMinimizeAgg;
typedef IntVarRange CPIntVarRange;
typedef IntVarRange InnerIntVarRange;
typedef IntVarEnum CPIntVarEnum;
typedef IntVarEnum InnerIntVarEnum;
typedef BinaryRel<Atom> CPBinaryRel;
typedef BinaryRel<int> InnerCPBinaryRel;
typedef BinaryRelVar<Atom> CPBinaryRelVar;
typedef BinaryRelVar<int> InnerCPBinaryRelVar;
typedef SumWeighted<Atom> CPSumWeighted;
typedef SumWeighted<int> InnerCPSumWeighted;
typedef Count CPCount;
typedef Count InnerCPCount;
typedef AllDiff CPAllDiff;
typedef AllDiff InnerCPAllDiff;
typedef M<Lit> InnerModel;
typedef M<Literal> Model;
typedef std::vector<Model*> modellist;
typedef WLtuple<Lit> WL;

}

#endif /* DATASTRUCTURES_HPP_ */
