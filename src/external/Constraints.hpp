/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

// IMPORTANT NOTE: Uses remapping, so never use for internal constraint creation!!!

#include "Space.hpp"

namespace MinisatID {

VarID map(VarID var, Remapper& remapper);
Atom map(const Atom& atom, Remapper& remapper);
Lit map(const Lit& lit, Remapper& remapper);

template<class Elem>
std::vector<Elem> map(const std::vector<Elem>& lits, Remapper& remapper) {
	std::vector<Elem> ll;
	ll.reserve(lits.size());
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(map(*i, remapper));
	}
	return ll;
}

std::vector<std::vector<Lit> > map(const std::vector<std::vector<Lit> >& lits, Remapper& remapper);
std::map<Lit, Lit> map(const std::map<Lit, Lit>& lits, Remapper& remapper);
std::map<Atom, Atom> map(const std::map<Atom, Atom>& atoms, Remapper& remapper);

template<typename Constraint, typename Engine>
class ExtAdd {
public:
	void extAdd(Engine& space, const Constraint& obj);
};

template<typename Constraint, typename Engine>
void extAdd(Engine& space, const Constraint& obj) {
	ExtAdd<Constraint, Engine> f;
	f.extAdd(space, obj);
}

template<typename Engine>
class ExtAdd<Disjunction, Engine> {
public:
	void extAdd(Engine& space, const Disjunction& obj) {
		space.add(Disjunction(obj.getID(), map(obj.literals, *space.getRemapper())));
	}
};

template<typename Engine>
class ExtAdd<Implication, Engine> {
public:
	void extAdd(Engine& space, const Implication& obj) {
		auto& s = *space.getRemapper();
		Implication eq(obj.getID(), map(obj.head, s), obj.type, map(obj.body, s), obj.conjunction);
		space.add(eq);
	}
};

template<typename Engine>
class ExtAdd<Rule, Engine> {
public:
	void extAdd(Engine& space, const Rule& obj) {
		auto& s = *space.getRemapper();
		Rule rule(obj.getID(), map(obj.head, s), map(obj.body, s), obj.conjunctive, obj.definitionID);
		space.add(rule);
	}
};
template<typename Engine>
class ExtAdd<WLSet, Engine> {
public:
	void extAdd(Engine& space, const WLSet& obj) {
		WLSet set(obj.setID);
		if (obj.setID < 0) {
			throw idpexception("External sets should have a positive id.");
		}
		for (auto i = obj.wl.cbegin(); i < obj.wl.cend(); ++i) {
			set.wl.push_back(WLtuple(map((*i).l, *space.getRemapper()), (*i).w));
		}
		space.add(set);
	}
};
template<typename Engine>
class ExtAdd<Aggregate, Engine> {
public:
	void extAdd(Engine& space, const Aggregate& obj) {
		space.add(Aggregate(obj.getID(), map(obj.head, *space.getRemapper()), obj.setID, obj.bound, obj.type, obj.sign, obj.sem, obj.defID));
	}
};
template<typename Engine>
class ExtAdd<MinimizeSubset, Engine> {
public:
	void extAdd(Engine& space, const MinimizeSubset& obj) {
		space.add(MinimizeSubset(obj.priority, map(obj.literals, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<MinimizeOrderedList, Engine> {
public:
	void extAdd(Engine& space, const MinimizeOrderedList& obj) {
		space.add(MinimizeOrderedList(obj.priority, map(obj.literals, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<MinimizeVar, Engine> {
public:
	void extAdd(Engine& space, const MinimizeVar& obj) {
		space.add(MinimizeVar( obj.priority, map(obj.varID, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<MinimizeAgg, Engine> {
public:
	void extAdd(Engine& space, const MinimizeAgg& obj) {
		space.add(obj);
	}
};
template<typename Engine>
class ExtAdd<Symmetry, Engine> {
public:
	void extAdd(Engine& space, const Symmetry& obj) {
		space.add(Symmetry(map(obj.symmetry, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<LazyGroundLit, Engine> {
public:
	void extAdd(Engine& space, const LazyGroundLit& obj) {
		LazyGroundLit lc(obj.watchboth, map(obj.residual, *space.getRemapper()), obj.monitor);
		space.add(lc);
	}
};
template<typename Engine>
class ExtAdd<LazyGroundImpl, Engine> {
public:
	void extAdd(Engine& space, const LazyGroundImpl& obj) {
		auto& r = *space.getRemapper();
		space.add(
				LazyGroundImpl(obj.getID(),
						Implication(obj.impl.getID(), map(obj.impl.head, r), obj.impl.type, map(obj.impl.body, r), obj.impl.conjunction),
						obj.monitor,
						obj.clauseID));
	}
};
template<typename Engine>
class ExtAdd<LazyAddition, Engine> {
public:
	void extAdd(Engine& space, const LazyAddition& obj) {
		space.add(LazyAddition(map(obj.list, *space.getRemapper()), obj.ref));
	}
};
template<typename Engine>
class ExtAdd<IntVarEnum, Engine> {
public:
	void extAdd(Engine& space, const IntVarEnum& obj) {
		space.add(IntVarEnum(obj.getID(), map(obj.varID, *space.getRemapper()), obj.values));
	}
};
template<typename Engine>
class ExtAdd<IntVarRange, Engine> {
public:
	void extAdd(Engine& space, const IntVarRange& obj) {
		space.add(IntVarRange(obj.getID(), map(obj.varID, *space.getRemapper()), obj.minvalue, obj.maxvalue));
	}
};
template<typename Engine>
class ExtAdd<CPBinaryRel, Engine> {
public:
	void extAdd(Engine& space, const CPBinaryRel& obj) {
		auto& s = *space.getRemapper();
		CPBinaryRel form(obj.getID(), map(obj.head, s), map(obj.varID, s), obj.rel, obj.bound);
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPBinaryRelVar, Engine> {
public:
	void extAdd(Engine& space, const CPBinaryRelVar& obj) {
		auto& s = *space.getRemapper();
		CPBinaryRelVar form(obj.getID(), map(obj.head, s), map(obj.lhsvarID, s), obj.rel, map(obj.rhsvarID, s));
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPSumWeighted, Engine> {
public:
	void extAdd(Engine& space, const CPSumWeighted& obj) {
		auto& s = *space.getRemapper();
		CPSumWeighted form(obj.getID(), map(obj.head, s), map(obj.varIDs, s), obj.weights, obj.rel, obj.bound);
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPProdWeighted, Engine> {
public:
	void extAdd(Engine& space, const CPProdWeighted& obj) {
		auto& s = *space.getRemapper();
		CPProdWeighted form(obj.getID(), map(obj.head, s), map(obj.varIDs, s), obj.prodWeight, obj.rel, map(obj.boundID,s));
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPCount, Engine> {
public:
	void extAdd(Engine& space, const CPCount& obj) {
		auto& s = *space.getRemapper();
		space.add(CPCount(obj.getID(), map(obj.varIDs, s), obj.eqbound, obj.rel, map(obj.rhsvar, s)));
	}
};
template<typename Engine>
class ExtAdd<CPElement, Engine> {
public:
	void extAdd(Engine& space, const CPElement& obj) {
		auto& s = *space.getRemapper();
		space.add(CPElement(obj.getID(), map(obj.varIDs, s), map(obj.index, s), map(obj.rhs, s)));
	}
};
template<typename Engine>
class ExtAdd<CPAllDiff, Engine> {
public:
	void extAdd(Engine& space, const CPAllDiff& obj) {
		auto& s = *space.getRemapper();
		space.add(CPAllDiff(obj.getID(), map(obj.varIDs, s)));
	}
};

template<typename Engine>
Value extGetValue(Engine& space, const Lit& obj) {
	return space.getValue(map(obj, *space.getRemapper()));
}
}
