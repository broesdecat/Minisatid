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
void add(ConstraintAdditionInterface<Engine>& space, const Disjunction& obj) {
	space.getEngine()->add(Disjunction(checkLits(obj.literals, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Implication& obj) {
	Implication eq(checkLit(obj.head, space.getRemapper()), obj.type, checkLits(obj.body, space.getRemapper()), obj.conjunction);
	space.getEngine()->add(eq);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Rule& obj) {
	Rule rule;
	rule.head = checkAtom(obj.head, space.getRemapper());
	rule.definitionID = obj.definitionID;
	rule.conjunctive = obj.conjunctive;
	rule.body = checkLits(obj.body, space.getRemapper());
	space.getEngine()->add(rule);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const WLSet& obj) {
	WLSet set;
	set.setID = obj.setID;
	for (auto i = obj.wl.cbegin(); i < obj.wl.cend(); ++i) {
		set.wl.push_back(WLtuple(checkLit((*i).l, space.getRemapper()), (*i).w));
	}
	space.getEngine()->add(set);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Aggregate& obj) {
	space.getEngine()->add(
			Aggregate(checkAtom(obj.head, space.getRemapper()), obj.setID, obj.bound, obj.type, obj.sign, obj.sem, obj.defID));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeSubset& obj) {
	space.getEngine()->add(MinimizeSubset(obj.priority, checkLits(obj.literals, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeOrderedList& obj) {
	space.getEngine()->add(MinimizeOrderedList(obj.priority, checkLits(obj.literals, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeVar& obj) {
	space.getEngine()->add(MinimizeVar(obj.priority, obj.varID));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeAgg& obj) {
	space.getEngine()->add(MinimizeAgg(obj.priority, obj.setid, obj.type));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Symmetry& obj) {
	space.getEngine()->add(Symmetry(checkLits(obj.symmetry, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const LazyGroundLit& obj) {
	LazyGroundLit lc(obj.watchboth, checkLit(obj.residual, space.getRemapper()), obj.monitor);
	//clog <<"Watching " <<(lc.watchboth?"both":"single") <<" on " <<lc.residual <<"\n";
	space.getEngine()->add(lc);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const IntVarEnum& obj) {
	IntVarEnum var;
	var.varID = obj.varID;
	var.values = obj.values;
	space.getEngine()->add(var);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const IntVarRange& obj) {
	IntVarRange var;
	var.varID = obj.varID;
	var.minvalue = obj.minvalue;
	var.maxvalue = obj.maxvalue;
	space.getEngine()->add(var);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPBinaryRel& obj) {
	CPBinaryRel form;
	form.head = checkAtom(obj.head, space.getRemapper());
	form.varID = obj.varID;
	form.rel = obj.rel;
	form.bound = obj.bound;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPBinaryRelVar& obj) {
	CPBinaryRelVar form;
	form.head = checkAtom(obj.head, space.getRemapper());
	form.lhsvarID = obj.lhsvarID;
	form.rel = obj.rel;
	form.rhsvarID = obj.rhsvarID;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPSumWeighted& obj) {
	CPSumWeighted form;
	form.head = checkAtom(obj.head, space.getRemapper());
	form.rel = obj.rel;
	form.bound = obj.bound;
	form.weights = obj.weights;
	form.varIDs = obj.varIDs;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPCount& obj) {
	CPCount form;
	form.varIDs = obj.varIDs;
	form.eqbound = obj.eqbound;
	form.rel = obj.rel;
	form.rhsvar = obj.rhsvar;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPAllDiff& obj) {
	CPAllDiff form(obj.varIDs);
	space.getEngine()->add(form);
}
}

#endif /* CONSTRAINTS_HPP_ */
