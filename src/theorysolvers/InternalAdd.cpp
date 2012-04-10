/************************************
 InternalAdd.cpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#include "InternalAdd.hpp"
#include "theorysolvers/PCSolver.hpp"

using namespace std;

namespace MinisatID{

void addVars(const std::vector<Var>& vars, ConstraintDatabase& engine) {
	for (auto i = vars.cbegin(); i < vars.cend(); ++i) {
		engine.createVar(*i);
	}
}

template<typename T>
void internalAdd(const T& obj, ConstraintDatabase& engine){
	addVars(obj.getAtoms(), engine);
	engine.getFactory().add(obj);
}

void add(const Disjunction& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}

void add(const Implication& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const Rule& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const WLSet& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const Aggregate& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const MinimizeSubset& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const MinimizeOrderedList& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const MinimizeVar& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const MinimizeAgg& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const Symmetry& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const LazyGroundLit& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const IntVarEnum& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const IntVarRange& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const CPBinaryRel& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const CPBinaryRelVar& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const CPSumWeighted& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const CPCount& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}
void add(const CPAllDiff& obj, ConstraintDatabase& engine) {
	internalAdd(obj, engine);
}

}
