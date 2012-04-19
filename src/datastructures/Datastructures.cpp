#include "external/Datastructures.hpp"
#include "space/Remapper.hpp"
#include "external/Constraints.hpp"
#include "constraintvisitors/ConstraintVisitor.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID{
	bool isPositive(const Lit& lit){
		return not sign(lit);
	}
	bool isNegative(const Lit& lit){
		return sign(lit);
	}

	int ID::nextid = 1;

	WLSet createSet(int setid, const std::vector<Lit>& literals, const Weight& w){
		WLSet set(setid);
		for(auto i=literals.cbegin(); i<literals.cend(); ++i) {
			set.wl.push_back({*i, w});
		}
		return set;
	}
	WLSet createSet(int setid, const std::vector<Lit>& literals, const std::vector<Weight>& weights){
		MAssert(literals.size()==weights.size());
		WLSet set(setid);
		auto wit = weights.cbegin();
		auto lit = literals.cbegin();
		for(; lit<literals.cend(); ++lit, ++wit) {
			set.wl.push_back({*lit, *wit});
		}
		return set;
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
	DATASTRUCTURE_ACCEPT(IntVarEnum)
	DATASTRUCTURE_ACCEPT(IntVarRange)
	DATASTRUCTURE_ACCEPT(LazyGroundLit)

}
