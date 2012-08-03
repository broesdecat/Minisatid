/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CONSTRAINTS_HPP_
#define CONSTRAINTS_HPP_

// IMPORTANT NOTE: Uses remapping, so never use for internal constraint creation!!!

#include "Space.hpp"

namespace MinisatID {

Atom checkAtom(const Atom& atom, Remapper& remapper);
Lit checkLit(const Lit& lit, Remapper& remapper);
std::vector<Lit> checkLits(const std::vector<Lit>& lits, Remapper& remapper);
std::vector<std::vector<Lit> > checkLits(const std::vector<std::vector<Lit> >& lits, Remapper& remapper);
std::map<Lit, Lit> checkLits(const std::map<Lit, Lit>& lits, Remapper& remapper);
std::vector<Atom> checkAtoms(const std::vector<Atom>& atoms, Remapper& remapper);
std::map<Atom, Atom> checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper);

template<typename Constraint, typename Engine>
class ExtAdd{
public:
	void extAdd(Engine& space, const Constraint& obj);
};

template<typename Constraint, typename Engine>
void extAdd(Engine& space, const Constraint& obj){
	ExtAdd<Constraint, Engine> f;
	f.extAdd(space, obj);
}

template<typename Engine>
class ExtAdd<Disjunction, Engine> {
public:
	void extAdd(Engine& space, const Disjunction& obj) {
		space.add(Disjunction(checkLits(obj.literals, *space.getRemapper())));
	}
};

template<typename Engine>
class ExtAdd<Implication, Engine> {
public:
	void extAdd(Engine& space, const Implication& obj) {
		Implication eq(checkLit(obj.head, *space.getRemapper()), obj.type, checkLits(obj.body, *space.getRemapper()), obj.conjunction);
		space.add(eq);
	}
};

template<typename Engine>
class ExtAdd<Rule, Engine> {
public:
	void extAdd(Engine& space, const Rule& obj) {
		Rule rule(checkAtom(obj.head, *space.getRemapper()), checkLits(obj.body, *space.getRemapper()), obj.conjunctive, obj.definitionID);
		space.add(rule);
	}
};
template<typename Engine>
class ExtAdd<WLSet, Engine> {
public:
	void extAdd(Engine& space, const WLSet& obj) {
		WLSet set(obj.setID);
		if(obj.setID<0){
			throw idpexception("External sets should have a positive id.");
		}
		for (auto i = obj.wl.cbegin(); i < obj.wl.cend(); ++i) {
			set.wl.push_back(WLtuple(checkLit((*i).l, *space.getRemapper()), (*i).w));
		}
		space.add(set);
	}
};
template<typename Engine>
class ExtAdd<Aggregate, Engine> {
public:
	void extAdd(Engine& space, const Aggregate& obj) {
		space.add(Aggregate(checkLit(obj.head, *space.getRemapper()), obj.setID, obj.bound, obj.type, obj.sign, obj.sem, obj.defID));
	}
};
template<typename Engine>
class ExtAdd<MinimizeSubset, Engine> {
public:
	void extAdd(Engine& space, const MinimizeSubset& obj) {
		space.add(MinimizeSubset(obj.priority, checkLits(obj.literals, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<MinimizeOrderedList, Engine> {
public:
	void extAdd(Engine& space, const MinimizeOrderedList& obj) {
		space.add(MinimizeOrderedList(obj.priority, checkLits(obj.literals, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<MinimizeVar, Engine> {
public:
	void extAdd(Engine& space, const MinimizeVar& obj) {
		space.add(obj);
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
		space.add(Symmetry(checkLits(obj.symmetry, *space.getRemapper())));
	}
};
template<typename Engine>
class ExtAdd<LazyGroundLit, Engine> {
public:
	void extAdd(Engine& space, const LazyGroundLit& obj) {
		LazyGroundLit lc(obj.watchboth, checkLit(obj.residual, *space.getRemapper()), obj.monitor);
		//clog <<"Watching " <<(lc.watchboth?"both":"single") <<" on " <<lc.residual <<"\n";
		space.add(lc);
	}
};
template<typename Engine>
class ExtAdd<LazyGroundImpl, Engine> {
public:
	void extAdd(Engine& space, const LazyGroundImpl& obj) {
		auto& r = *space.getRemapper();
		space.add(LazyGroundImpl(Implication(checkLit(obj.impl.head, r), obj.impl.type, checkLits(obj.impl.body, r), obj.impl.conjunction), obj.monitor));
	}
};
template<typename Engine>
class ExtAdd<LazyAddition, Engine> {
public:
	void extAdd(Engine& space, const LazyAddition& obj) {
		space.add(LazyAddition(checkLits(obj.list, *space.getRemapper()), obj.ref));
	}
};
template<typename Engine>
class ExtAdd<IntVarEnum, Engine> {
public:
	void extAdd(Engine& space, const IntVarEnum& obj) {
		space.add(obj);
	}
};
template<typename Engine>
class ExtAdd<IntVarRange, Engine> {
public:
	void extAdd(Engine& space, const IntVarRange& obj) {
		space.add(obj);
	}
};
template<typename Engine>
class ExtAdd<CPBinaryRel, Engine> {
public:
	void extAdd(Engine& space, const CPBinaryRel& obj) {
		CPBinaryRel form(checkAtom(obj.head, *space.getRemapper()), obj.varID, obj.rel, obj.bound);
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPBinaryRelVar, Engine> {
public:
	void extAdd(Engine& space, const CPBinaryRelVar& obj) {
		CPBinaryRelVar form(checkAtom(obj.head, *space.getRemapper()), obj.lhsvarID, obj.rel, obj.rhsvarID);
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPSumWeighted, Engine> {
public:
	void extAdd(Engine& space, const CPSumWeighted& obj) {
		CPSumWeighted form(checkAtom(obj.head, *space.getRemapper()), obj.varIDs, obj.weights, obj.rel, obj.bound);
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPProdWeighted, Engine> {
public:
	void extAdd(Engine& space, const CPProdWeighted& obj) {
		CPProdWeighted form(checkAtom(obj.head, *space.getRemapper()), obj.varIDs, obj.prodWeight, obj.rel, obj.bound);
		space.add(form);
	}
};
template<typename Engine>
class ExtAdd<CPCount, Engine> {
public:
	void extAdd(Engine& space, const CPCount& obj) {
		space.add(obj);
	}
};
template<typename Engine>
class ExtAdd<CPElement, Engine> {
public:
	void extAdd(Engine& space, const CPElement& obj) {
		space.add(obj);
	}
};
template<typename Engine>
class ExtAdd<CPAllDiff, Engine> {
public:
	void extAdd(Engine& space, const CPAllDiff& obj) {
		space.add(obj);
	}
};

template<typename Engine>
Value extGetValue(Engine& space, const Lit& obj){
	return space.getValue(checkLit(obj, *space.getRemapper()));
}
}

#endif /* CONSTRAINTS_HPP_ */
