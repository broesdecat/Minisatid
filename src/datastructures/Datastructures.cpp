#include "external/Datastructures.hpp"
#include "space/Remapper.hpp"
#include "external/Constraints.hpp"
#include "external/ConstraintVisitor.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID {

std::ostream& operator<<(std::ostream& stream, Value val) {
	switch (val) {
	case Value::True:
		stream << "true";
		break;
	case Value::False:
		stream << "false";
		break;
	case Value::Unknown:
		stream << "unknown";
		break;
	}
	return stream;
}

bool isPositive(const Lit& lit) {
	return not sign(lit);
}
bool isNegative(const Lit& lit) {
	return sign(lit);
}

EqType invertEqType(EqType type) {
	switch (type) {
	case EqType::EQ:
	case EqType::NEQ:
		return type;
	case EqType::L:
		return EqType::G;
	case EqType::G:
		return EqType::L;
	case EqType::GEQ:
		return EqType::LEQ;
	case EqType::LEQ:
		return EqType::GEQ;
	}
	MAssert(false);
	return EqType::EQ;
}

WLSet createSet(int setid, const std::vector<Lit>& literals, const Weight& w) {
	WLSet set(setid);
	for (auto l : literals) {
		set.wl.push_back( { l, w });
	}
	return set;
}
WLSet createSet(int setid, const std::vector<Lit>& literals, const std::vector<Weight>& weights) {
	MAssert(literals.size()==weights.size());
	WLSet set(setid);
	auto wit = weights.cbegin();
	auto lit = literals.cbegin();
	for (; lit < literals.cend(); ++lit, ++wit) {
		set.wl.push_back( { *lit, *wit });
	}
	return set;
}

void addImplication(const Lit& head, const litlist& body, bool conjunction, std::vector<Disjunction>& clauses) {
	if (conjunction) {
		Disjunction d({ });
		d.literals.resize(2, not head);
		for (auto l : body) {
			d.literals[1] = l;
			clauses.push_back(d);
		}
	} else {
		Disjunction d(body);
		d.literals.push_back(not head);
		clauses.push_back(d);
	}
}

// Precondition: already added vars!
void addReverseImplication(const Lit& head, const litlist& body, bool conjunction, std::vector<Disjunction>& clauses) {
	litlist list;
	for (auto l : body) {
		list.push_back(not l);
	}
	addImplication(not head, list, not conjunction, clauses);
}

std::vector<Disjunction> Implication::getEquivalentClauses() const {
	std::vector<Disjunction> clauses;
	switch (type) {
	case ImplicationType::EQUIVALENT:
		addImplication(head, body, conjunction, clauses);
		addReverseImplication(head, body, conjunction, clauses);
		break;
	case ImplicationType::IMPLIES:
		addImplication(head, body, conjunction, clauses);
		break;
	case ImplicationType::IMPLIEDBY:
		addReverseImplication(head, body, conjunction, clauses);
		break;
	}
	return clauses;
}

#define DATASTRUCTURE_ACCEPT(x) \
void x::accept(ConstraintVisitor* visitor){\
	visitor->add(*this);\
}\
void x::accept(Space* visitor){\
	extAdd(*visitor, *this);\
}

DATASTRUCTURE_ACCEPT(Disjunction)
DATASTRUCTURE_ACCEPT(Implication)
DATASTRUCTURE_ACCEPT(Rule)
DATASTRUCTURE_ACCEPT(Aggregate)
DATASTRUCTURE_ACCEPT(WLSet)
DATASTRUCTURE_ACCEPT(Symmetry)
DATASTRUCTURE_ACCEPT(OptimizeVar)
DATASTRUCTURE_ACCEPT(MinimizeSubset)
DATASTRUCTURE_ACCEPT(MinimizeOrderedList)
DATASTRUCTURE_ACCEPT(MinimizeAgg)
DATASTRUCTURE_ACCEPT(CPCount)
DATASTRUCTURE_ACCEPT(CPBinaryRel)
DATASTRUCTURE_ACCEPT(CPBinaryRelVar)
DATASTRUCTURE_ACCEPT(CPAllDiff)
DATASTRUCTURE_ACCEPT(CPSumWeighted)
DATASTRUCTURE_ACCEPT(CPProdWeighted)
DATASTRUCTURE_ACCEPT(CPElement)
DATASTRUCTURE_ACCEPT(BoolVar)
DATASTRUCTURE_ACCEPT(IntVarEnum)
DATASTRUCTURE_ACCEPT(IntVarRange)
DATASTRUCTURE_ACCEPT(LazyGroundLit)
DATASTRUCTURE_ACCEPT(LazyGroundImpl)
DATASTRUCTURE_ACCEPT(LazyAddition)
DATASTRUCTURE_ACCEPT(SubTheory)
DATASTRUCTURE_ACCEPT(TwoValuedRequirement)
DATASTRUCTURE_ACCEPT(LazyAtom)

// constructor used when passing data from grounder to solver
// TODO: check whether it satisfies the right constraints (e.g.: no literal is mapped to itself, commuting with negation) => currently solved in the getSymmetry method
Symmetry::Symmetry(const std::map<Lit, Lit>& s)
		: symmetry(s) {
}

// alternative constructor which takes disjoint cycles as input, used by the parser.
// precondition: the input is actually a disjoint cycle (no literal present in two cycles)
Symmetry::Symmetry(const std::vector<std::vector<Lit> >& s)
		: symmetry(std::map<Lit, Lit>()) {
	for (auto cycle : s) {
		for (uint i = 0; i < cycle.size(); ++i) {
			symmetry.insert( { cycle[i], cycle[(i + 1) % cycle.size()] });
		}
	}
}

// calculates a disjoint cycle data structure for this symmetry
void Symmetry::getCycles(std::vector<std::vector<Lit> >& dcn) const {
	dcn.clear();
	std::set<Lit> literalsInCycles;
	for (auto litpair : symmetry) {
		Lit first = litpair.first;
		if (literalsInCycles.count(first) == 0) {
			std::vector<Lit> newCycle;
			while (literalsInCycles.insert(first).second) {
				newCycle.push_back(first);
				first = symmetry.at(first);
			}
			dcn.push_back(newCycle);
		}
	}
}

std::unordered_map<Lit,Lit> Symmetry::getSymmetrical() const{
	std::unordered_map<Lit,Lit> result;
	for(auto litpair:symmetry){
		if(litpair.first!=litpair.second){
			result.insert({litpair.first,litpair.second});
			result.insert({not litpair.first,not litpair.second});
		}
	}
	return result;
}

std::unordered_map<Lit,Lit> Symmetry::getInverse() const{
	std::unordered_map<Lit,Lit> result;
	for(auto litpair:symmetry){
		if(litpair.first!=litpair.second){
			result.insert({litpair.second,litpair.first});
			result.insert({not litpair.second,not litpair.first});
		}
	}
	return result;
}

}
