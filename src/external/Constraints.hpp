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

Var checkAtom(const Atom& atom, Remapper& remapper);
Lit checkLit(const Literal& lit, Remapper& remapper);
std::vector<Lit> checkLits(const std::vector<Literal>& lits, Remapper& remapper);
std::vector<std::vector<Lit> > checkLits(const std::vector<std::vector<Literal> >& lits, Remapper& remapper);
std::map<Lit, Lit> checkLits(const std::map<Literal, Literal>& lits, Remapper& remapper);
std::vector<Var> checkAtoms(const std::vector<Atom>& atoms, Remapper& remapper);
std::map<Var, Var> checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper);

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Disjunction& sentence) {
	space.getEngine()->add(Disjunction(checkLits(sentence.literals, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Implication& sentence) {
	Implication eq(checkLit(sentence.head, space.getRemapper()), sentence.type, checkLits(sentence.body, space.getRemapper()), sentence.conjunction);
	space.getEngine()->add(eq);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Rule& sentence) {
	Rule rule;
	rule.head = checkAtom(sentence.head, space.getRemapper());
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	rule.body = checkLits(sentence.body, space.getRemapper());
	space.getEngine()->add(rule);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const WLSet& sentence) {
	WLSet set;
	set.setID = sentence.setID;
	for (auto i = sentence.wl.cbegin(); i < sentence.wl.cend(); ++i) {
		set.wl.push_back(WLtuple(checkLit((*i).l, space.getRemapper()), (*i).w));
	}
	space.getEngine()->add(set);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Aggregate& sentence) {
	Aggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head, space.getRemapper());
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	space.getEngine()->add(agg);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeSubset& sentence) {
	space.getEngine()->add(MinimizeSubset(sentence.priority, checkLits(sentence.literals, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeOrderedList& sentence) {
	space.getEngine()->add(MinimizeOrderedList(sentence.priority, checkLits(sentence.literals, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeVar& sentence) {
	space.getEngine()->add(MinimizeVar(sentence.priority, sentence.varID));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const MinimizeAgg& sentence) {
	space.getEngine()->add(MinimizeAgg(sentence.priority, sentence.setid, sentence.type));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const Symmetry& sentence) {
	space.getEngine()->add(Symmetry(checkLits(sentence.symmetry, space.getRemapper())));
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const LazyGroundLit& sentence) {
	LazyGroundLit lc(sentence.watchboth, checkLit(sentence.residual, space.getRemapper()), sentence.monitor);
	//clog <<"Watching " <<(lc.watchboth?"both":"single") <<" on " <<lc.residual <<"\n";
	space.getEngine()->add(lc);
}

template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const IntVarEnum& sentence) {
	IntVarEnum var;
	var.varID = sentence.varID;
	var.values = sentence.values;
	space.getEngine()->add(var);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const IntVarRange& sentence) {
	IntVarRange var;
	var.varID = sentence.varID;
	var.minvalue = sentence.minvalue;
	var.maxvalue = sentence.maxvalue;
	space.getEngine()->add(var);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPBinaryRel& sentence) {
	CPBinaryRel form;
	form.head = checkAtom(sentence.head, space.getRemapper());
	form.varID = sentence.varID;
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPBinaryRelVar& sentence) {
	CPBinaryRelVar form;
	form.head = checkAtom(sentence.head, space.getRemapper());
	form.lhsvarID = sentence.lhsvarID;
	form.rel = sentence.rel;
	form.rhsvarID = sentence.rhsvarID;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPSumWeighted& sentence) {
	CPSumWeighted form;
	form.head = checkAtom(sentence.head, space.getRemapper());
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	form.weights = sentence.weights;
	form.varIDs = sentence.varIDs;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPCount& sentence) {
	CPCount form;
	form.varIDs = sentence.varIDs;
	form.eqbound = sentence.eqbound;
	form.rel = sentence.rel;
	form.rhsvar = sentence.rhsvar;
	space.getEngine()->add(form);
}
template<typename Engine>
void add(ConstraintAdditionInterface<Engine>& space, const CPAllDiff& sentence) {
	CPAllDiff form(sentence.varIDs);
	space.getEngine()->add(form);
}
}

#endif /* CONSTRAINTS_HPP_ */
