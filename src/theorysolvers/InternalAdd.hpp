/************************************
	InternalAdd.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#ifndef INTERNALADD_HPP_
#define INTERNALADD_HPP_

#include "external/ExternalUtils.hpp"

namespace MinisatID{
class ConstraintDatabase;
void add(const Disjunction& obj, ConstraintDatabase& engine);
void add(const Implication& obj, ConstraintDatabase& engine);
void add(const Rule& obj, ConstraintDatabase& engine);
void add(const WLSet& obj, ConstraintDatabase& engine);
void add(const Aggregate& obj, ConstraintDatabase& engine);
void add(const MinimizeSubset& obj, ConstraintDatabase& engine);
void add(const MinimizeOrderedList& obj, ConstraintDatabase& engine);
void add(const MinimizeVar& obj, ConstraintDatabase& engine);
void add(const MinimizeAgg& obj, ConstraintDatabase& engine);
void add(const Symmetry& obj, ConstraintDatabase& engine);
void add(const LazyGroundLit& obj, ConstraintDatabase& engine);
void add(const IntVarEnum& obj, ConstraintDatabase& engine);
void add(const IntVarRange& obj, ConstraintDatabase& engine);
void add(const CPBinaryRel& obj, ConstraintDatabase& engine);
void add(const CPBinaryRelVar& obj, ConstraintDatabase& engine);
void add(const CPSumWeighted& obj, ConstraintDatabase& engine);
void add(const CPCount& obj, ConstraintDatabase& engine);
void add(const CPAllDiff& obj, ConstraintDatabase& engine);
}

#endif /* INTERNALADD_HPP_ */
