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
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		set.wl.push_back( { *i, w });
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

void addImplication(uint id, const Lit& head, const litlist& body, bool conjunction, std::vector<Disjunction>& clauses) {
	if (conjunction) {
		Disjunction d(id, { });
		d.literals.resize(2, not head);
		for (auto i = body.cbegin(); i < body.cend(); ++i) {
			d.literals[1] = *i;
			clauses.push_back(d);
		}
	} else {
		Disjunction d(id, body);
		d.literals.push_back(not head);
		clauses.push_back(d);
	}
}

// Precondition: already added vars!
void addReverseImplication(uint id, const Lit& head, const litlist& body, bool conjunction, std::vector<Disjunction>& clauses) {
	litlist list;
	for (auto i = body.cbegin(); i < body.cend(); ++i) {
		list.push_back(not *i);
	}
	addImplication(id, not head, list, not conjunction, clauses);
}

std::vector<Disjunction> Implication::getEquivalentClauses() const {
	std::vector<Disjunction> clauses;
	switch (type) {
	case ImplicationType::EQUIVALENT:
		addImplication(getID(), head, body, conjunction, clauses);
		addReverseImplication(getID(), head, body, conjunction, clauses);
		break;
	case ImplicationType::IMPLIES:
		addImplication(getID(), head, body, conjunction, clauses);
		break;
	case ImplicationType::IMPLIEDBY:
		addReverseImplication(getID(), head, body, conjunction, clauses);
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
DATASTRUCTURE_ACCEPT(MinimizeVar)
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
}
