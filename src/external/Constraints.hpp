/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
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

template<typename Constraint, typename Remapper>
class ExtAdd {
public:
	Constraint extAdd(Remapper& r, const Constraint& obj);
};

template<typename Constraint, typename Engine>
void extAdd(Engine& space, const Constraint& obj) {
	ExtAdd<Constraint, Remapper> f;
	auto constraint = f.extAdd(*space.getRemapper(), obj);
	constraint.theoryid = obj.theoryid;
	space.add(constraint);
}

template<typename Remapper>
class ExtAdd<Disjunction, Remapper> {
public:
	Disjunction extAdd(Remapper& r, const Disjunction& obj) {
		return Disjunction(map(obj.literals, r));
	}
};

template<typename Remapper>
class ExtAdd<Implication, Remapper> {
public:
	Implication extAdd(Remapper& r, const Implication& obj) {
		return Implication(map(obj.head, r), obj.type, map(obj.body, r), obj.conjunction);
	}
};

template<typename Remapper>
class ExtAdd<Rule, Remapper> {
public:
	Rule extAdd(Remapper& r, const Rule& obj) {
		return Rule(map(obj.head, r), map(obj.body, r), obj.conjunctive, obj.definitionID, obj.onlyif);
	}
};
template<typename Remapper>
class ExtAdd<WLSet, Remapper> {
public:
	WLSet extAdd(Remapper& r, const WLSet& obj) {
		WLSet set(obj.setID);
		if (obj.setID < 0) {
			throw idpexception("External sets should have a positive id.");
		}
		for (auto i = obj.wl.cbegin(); i < obj.wl.cend(); ++i) {
			set.wl.push_back(WLtuple(map((*i).l, r), (*i).w));
		}
		return set;
	}
};
template<typename Remapper>
class ExtAdd<Aggregate, Remapper> {
public:
	Aggregate extAdd(Remapper& r, const Aggregate& obj) {
		return Aggregate(map(obj.head, r), obj.setID, obj.bound, obj.type, obj.sign, obj.sem, obj.defID, obj.onlyif);
	}
};
template<typename Remapper>
class ExtAdd<MinimizeSubset, Remapper> {
public:
	MinimizeSubset extAdd(Remapper& r, const MinimizeSubset& obj) {
		return MinimizeSubset(obj.priority, map(obj.literals, r));
	}
};
template<typename Remapper>
class ExtAdd<OptimizeVar, Remapper> {
public:
	OptimizeVar extAdd(Remapper& r, const OptimizeVar& obj) {
		return OptimizeVar( obj.priority, map(obj.varID, r), obj.minimize);
	}
};
template<typename Remapper>
class ExtAdd<MinimizeAgg, Remapper> {
public:
	MinimizeAgg extAdd(Remapper&, const MinimizeAgg& obj) {
		return obj;
	}
};
template<typename Remapper>
class ExtAdd<LazyGroundLit, Remapper> {
public:
	LazyGroundLit extAdd(Remapper& r, const LazyGroundLit& obj) {
		return LazyGroundLit(map(obj.residual, r), obj.watchedvalue, obj.monitor);
	}
};
template<typename Remapper>
class ExtAdd<LazyGroundImpl, Remapper> {
public:
	LazyGroundImpl extAdd(Remapper& r, const LazyGroundImpl& obj) {
		return LazyGroundImpl(Implication(map(obj.impl.head, r), obj.impl.type, map(obj.impl.body, r), obj.impl.conjunction), obj.monitor);
	}
};
template<typename Remapper>
class ExtAdd<LazyAddition, Remapper> {
public:
	LazyAddition extAdd(Remapper& r, const LazyAddition& obj) {
		return LazyAddition(map(obj.list, r), obj.ref);
	}
};
template<typename Remapper>
class ExtAdd<TwoValuedRequirement, Remapper> {
public:
	TwoValuedRequirement extAdd(Remapper& r, const TwoValuedRequirement& obj) {
		return TwoValuedRequirement(map(obj.atoms, r));
	}
};

template<typename Remapper>
class ExtAdd<TwoValuedVarIdRequirement, Remapper> {
public:
	TwoValuedVarIdRequirement extAdd(Remapper& r, const TwoValuedVarIdRequirement& obj) {
		return TwoValuedVarIdRequirement(map(obj.vid,r));
	}
};

template<typename Remapper>
class ExtAdd<BoolVar, Remapper> {
public:
	BoolVar extAdd(Remapper& r, const BoolVar& obj) {
		return BoolVar(map(obj.atom, r));
	}
};
template<typename Remapper>
class ExtAdd<IntVarEnum, Remapper> {
public:
	IntVarEnum extAdd(Remapper& r, const IntVarEnum& obj) {
		if(obj.partial){
			return IntVarEnum(map(obj.varID, r), obj.values, map(obj.possiblynondenoting, r));
		}else{
			return IntVarEnum(map(obj.varID, r), obj.values);
		}
	}
};
template<typename Remapper>
class ExtAdd<IntVarRange, Remapper> {
public:
	IntVarRange extAdd(Remapper& r, const IntVarRange& obj) {
		if(obj.partial){
			return IntVarRange(map(obj.varID, r), obj.minvalue, obj.maxvalue, map(obj.possiblynondenoting, r));
		}else{
			return IntVarRange(map(obj.varID, r), obj.minvalue, obj.maxvalue);
		}
	}
};
template<typename Remapper>
class ExtAdd<CPBinaryRel, Remapper> {
public:
	CPBinaryRel extAdd(Remapper& r, const CPBinaryRel& obj) {
		return CPBinaryRel(map(obj.head, r), map(obj.varID, r), obj.rel, obj.bound);
	}
};
template<typename Remapper>
class ExtAdd<CPBinaryRelVar, Remapper> {
public:
	CPBinaryRelVar extAdd(Remapper& r, const CPBinaryRelVar& obj) {
		return CPBinaryRelVar(map(obj.head, r), map(obj.lhsvarID, r), obj.rel, map(obj.rhsvarID, r));
	}
};
template<typename Remapper>
class ExtAdd<CPSumWeighted, Remapper> {
public:
	CPSumWeighted extAdd(Remapper& r, const CPSumWeighted& obj) {
		return CPSumWeighted(map(obj.head, r), map(obj.conditions, r), map(obj.varIDs, r), obj.weights, obj.rel, obj.bound);
	}
};
template<typename Remapper>
class ExtAdd<CPProdWeighted, Remapper> {
public:
	CPProdWeighted extAdd(Remapper& r, const CPProdWeighted& obj) {
		return CPProdWeighted(map(obj.head, r), map(obj.conditions, r), map(obj.varIDs, r), obj.prodWeight, obj.rel, map(obj.boundID,r));
	}
};
template<typename Remapper>
class ExtAdd<CPAllDiff, Remapper> {
public:
	CPAllDiff extAdd(Remapper& r, const CPAllDiff& obj) {
		return CPAllDiff(map(obj.varIDs, r));
	}
};
template<typename Remapper>
class ExtAdd<SubTheory, Remapper> {
public:
	SubTheory extAdd(Remapper& r, const SubTheory& obj) {
		return SubTheory(map(obj.head, r),obj.childid, map(obj.rigidatoms, r));
	}
};
template<typename Remapper>
class ExtAdd<LazyAtom, Remapper> {
public:
	LazyAtom extAdd(Remapper& r, const LazyAtom& obj) {
		return LazyAtom(map(obj.head, r), map(obj.args, r), obj.grounder);
	}
};

template<typename Engine>
Value extGetValue(Engine& space, const Lit& obj) {
	return space.getValue(map(obj, *space.getRemapper()));
}
}
