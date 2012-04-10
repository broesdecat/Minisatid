/************************************
 Constraints.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#ifndef CONSTRAINTS_HPP_
#define CONSTRAINTS_HPP_

// IMPORTANT NOTE: Uses remapping, so never use for internal constraint creation!!!

#include "Datastructures.hpp"
#include "Space.hpp"
#include "theorysolvers/InternalAdd.hpp"
#include <memory>

namespace MinisatID {
class PropAndBackMonitor;

Var checkAtom(const Atom& atom, Remapper& remapper);
Lit checkLit(const Literal& lit, Remapper& remapper);
std::vector<Lit> checkLits(const std::vector<Literal>& lits, Remapper& remapper);
std::vector<std::vector<Lit> > checkLits(const std::vector<std::vector<Literal> >& lits, Remapper& remapper);
std::map<Lit, Lit> checkLits(const std::map<Literal, Literal>& lits, Remapper& remapper);
std::vector<Var> checkAtoms(const std::vector<Atom>& atoms, Remapper& remapper);
std::map<Var, Var> checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper);

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const Disjunction& obj) {
	add(Disjunction(checkLits(obj.literals, space.getRemapper())), *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const Implication& obj) {
	Implication eq(checkLit(obj.head, space.getRemapper()), obj.type, checkLits(obj.body, space.getRemapper()), obj.conjunction);
	add(eq, *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const Rule& obj) {
	Rule rule;
	rule.head = checkAtom(obj.head, space.getRemapper());
	rule.definitionID = obj.definitionID;
	rule.conjunctive = obj.conjunctive;
	rule.body = checkLits(obj.body, space.getRemapper());
	add(rule, *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const WLSet& obj) {
	WLSet set;
	set.setID = obj.setID;
	for (auto i = obj.wl.cbegin(); i < obj.wl.cend(); ++i) {
		set.wl.push_back(WLtuple(checkLit((*i).l, space.getRemapper()), (*i).w));
	}
	add(set, *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const Aggregate& obj) {
	add(
			Aggregate(checkAtom(obj.head, space.getRemapper()), obj.setID, obj.bound, obj.type, obj.sign, obj.sem, obj.defID), *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeSubset& obj) {
	add(MinimizeSubset(obj.priority, checkLits(obj.literals, space.getRemapper())), *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeOrderedList& obj) {
	add(MinimizeOrderedList(obj.priority, checkLits(obj.literals, space.getRemapper())), *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeVar& obj) {
	add(obj, *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeAgg& obj) {
	add(obj, *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const Symmetry& obj) {
	add(Symmetry(checkLits(obj.symmetry, space.getRemapper())), *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const LazyGroundLit& obj) {
	LazyGroundLit lc(obj.watchboth, checkLit(obj.residual, space.getRemapper()), obj.monitor);
	//clog <<"Watching " <<(lc.watchboth?"both":"single") <<" on " <<lc.residual <<"\n";
	add(lc, *space.getEngine());
}

template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const IntVarEnum& obj) {
	add(obj, *space.getEngine());
}
template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const IntVarRange& obj) {
	add(obj, *space.getEngine());
}
template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const CPBinaryRel& obj) {
	CPBinaryRel form(checkAtom(obj.head, space.getRemapper()),obj.varID,obj.rel,obj.bound);
	add(form, *space.getEngine());
}
template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const CPBinaryRelVar& obj) {
	CPBinaryRelVar form(checkAtom(obj.head, space.getRemapper()), obj.lhsvarID, obj.rel, obj.rhsvarID);
	add(form, *space.getEngine());
}
template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const CPSumWeighted& obj) {
	CPSumWeighted form(checkAtom(obj.head, space.getRemapper()), obj.varIDs, obj.weights,obj.rel, obj.bound);
	add(form, *space.getEngine());
}
template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const CPCount& obj) {
	add(obj, *space.getEngine());
}
template<typename Engine>
void extAdd(ConstraintAdditionInterface<Engine>& space, const CPAllDiff& obj) {
	add(obj, *space.getEngine());
}
}

#endif /* CONSTRAINTS_HPP_ */
