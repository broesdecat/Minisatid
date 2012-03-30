/************************************
	Constraints.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#ifndef CONSTRAINTS_HPP_
#define CONSTRAINTS_HPP_

#include "Datastructures.hpp"
#include "Space.hpp"
#include <memory>

namespace MinisatID{
class PropAndBackMonitor;

void add(Space& space, const Disjunction& formula);
void add(Space& space, const Implication& formula);
void add(Space& space, const Rule& formula);
void add(Space& space, const Set& formula);
void add(Space& space, const WLSet& formula);
void add(Space& space, const WSet& formula);
void add(Space& space, const Aggregate& formula);
void add(Space& space, const Symmetry& formula);
void add(Space& space, const ForcedChoices& formula);
void add(Space& space, const MinimizeSubset& formula);
void add(Space& space, const MinimizeVar& formula);
void add(Space& space, const MinimizeOrderedList& formula);
void add(Space& space, const MinimizeAgg& formula);
void add(Space& space, const LazyGroundLit& formula);
void add(Space& space, const CPAllDiff& formula);
void add(Space& space, const CPBinaryRel& formula);
void add(Space& space, const CPBinaryRelVar& formula);
void add(Space& space, const CPCount& formula);
void add(Space& space, const CPIntVarEnum& formula);
void add(Space& space, const CPIntVarRange& formula);
void add(Space& space, const CPSumWeighted& formula);
void add(Space& space, PropAndBackMonitor* monitor);
}

#endif /* CONSTRAINTS_HPP_ */
