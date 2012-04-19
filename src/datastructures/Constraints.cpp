/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/Constraints.hpp"

#include "external/Remapper.hpp"
#include "external/Translator.hpp"
#include "space/SearchEngine.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "external/SearchMonitor.hpp"

#include "external/Datastructures.hpp"
#include "external/Space.hpp"
#include "datastructures/InternalAdd.hpp"
#include <memory>

#include <map>
#include <vector>

using namespace std;
using namespace MinisatID;

namespace MinisatID {

Var checkAtom(const Atom& atom, Remapper& remapper) {
	return remapper.getVar(atom);
}

Lit checkLit(const Literal& lit, Remapper& remapper) {
	return mkLit(checkAtom(lit.getAtom(), remapper), lit.hasSign());
}

vector<Lit> checkLits(const vector<Literal>& lits, Remapper& remapper) {
	vector<Lit> ll;
	ll.reserve(lits.size());
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLit(*i, remapper));
	}
	return ll;
}

vector<vector<Lit> > checkLits(const vector<vector<Literal> >& lits, Remapper& remapper) {
	vector<vector<Lit> > ll;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLits(*i, remapper));
	}
	return ll;
}

map<Lit, Lit> checkLits(const map<Literal, Literal>& lits, Remapper& remapper) {
	map<Lit, Lit> ll;
	for (auto i = lits.cbegin(); i != lits.cend(); ++i) {
		ll[checkLit(i->first, remapper)] = checkLit(i->second, remapper);
	}
	return ll;
}

vector<Var> checkAtoms(const vector<Atom>& atoms, Remapper& remapper) {
	vector<Var> ll;
	ll.reserve(atoms.size());
	for (auto i = atoms.cbegin(); i < atoms.cend(); ++i) {
		ll.push_back(checkAtom(*i, remapper));
	}
	return ll;
}

std::map<Var, Var> checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper) {
	std::map<Var, Var> ll;
	for (auto i = atoms.cbegin(); i != atoms.cend(); ++i) {
		ll.insert( { checkAtom((*i).first, remapper), checkAtom((*i).second, remapper) });
	}
	return ll;
}

template<typename Engine>
class ExtAdd<Disjunction, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const Disjunction& obj) {
		add(Disjunction(checkLits(obj.literals, space.getRemapper())), *space.getEngine());
	}
};

template<typename Engine>
class ExtAdd<Implication, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const Implication& obj) {
		Implication eq(checkLit(obj.head, space.getRemapper()), obj.type, checkLits(obj.body, space.getRemapper()), obj.conjunction);
		add(eq, *space.getEngine());
	}
};

template<typename Engine>
class ExtAdd<Rule, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const Rule& obj) {
		Rule rule;
		rule.head = checkAtom(obj.head, space.getRemapper());
		rule.definitionID = obj.definitionID;
		rule.conjunctive = obj.conjunctive;
		rule.body = checkLits(obj.body, space.getRemapper());
		add(rule, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<WLSet, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const WLSet& obj) {
		WLSet set(obj.setID);
		for (auto i = obj.wl.cbegin(); i < obj.wl.cend(); ++i) {
			set.wl.push_back(WLtuple(checkLit((*i).l, space.getRemapper()), (*i).w));
		}
		add(set, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<Aggregate, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const Aggregate& obj) {
		add(Aggregate(checkAtom(obj.head, space.getRemapper()), obj.setID, obj.bound, obj.type, obj.sign, obj.sem, obj.defID), *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<MinimizeSubset, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeSubset& obj) {
		add(MinimizeSubset(obj.priority, checkLits(obj.literals, space.getRemapper())), *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<MinimizeOrderedList, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeOrderedList& obj) {
		add(MinimizeOrderedList(obj.priority, checkLits(obj.literals, space.getRemapper())), *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<MinimizeVar, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeVar& obj) {
		add(obj, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<MinimizeAgg, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const MinimizeAgg& obj) {
		add(obj, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<Symmetry, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const Symmetry& obj) {
		add(Symmetry(checkLits(obj.symmetry, space.getRemapper())), *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<LazyGroundLit, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const LazyGroundLit& obj) {
		LazyGroundLit lc(obj.watchboth, checkLit(obj.residual, space.getRemapper()), obj.monitor);
		//clog <<"Watching " <<(lc.watchboth?"both":"single") <<" on " <<lc.residual <<"\n";
		add(lc, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<IntVarEnum, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const IntVarEnum& obj) {
		add(obj, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<IntVarRange, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const IntVarRange& obj) {
		add(obj, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<CPBinaryRel, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const CPBinaryRel& obj) {
		CPBinaryRel form(checkAtom(obj.head, space.getRemapper()), obj.varID, obj.rel, obj.bound);
		add(form, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<CPBinaryRelVar, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const CPBinaryRelVar& obj) {
		CPBinaryRelVar form(checkAtom(obj.head, space.getRemapper()), obj.lhsvarID, obj.rel, obj.rhsvarID);
		add(form, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<CPSumWeighted, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const CPSumWeighted& obj) {
		CPSumWeighted form(checkAtom(obj.head, space.getRemapper()), obj.varIDs, obj.weights, obj.rel, obj.bound);
		add(form, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<CPCount, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const CPCount& obj) {
		add(obj, *space.getEngine());
	}
};
template<typename Engine>
class ExtAdd<CPAllDiff, Engine> {
	void extAdd(ConstraintAdditionInterface<Engine>& space, const CPAllDiff& obj) {
		add(obj, *space.getEngine());
	}
};

template class ExtAdd<Disjunction, SearchEngine>;
template class ExtAdd<Implication, SearchEngine>;
template class ExtAdd<Rule, SearchEngine>;
template class ExtAdd<WLSet, SearchEngine>;
template class ExtAdd<Aggregate, SearchEngine>;
template class ExtAdd<MinimizeAgg, SearchEngine>;
template class ExtAdd<MinimizeVar, SearchEngine>;
template class ExtAdd<MinimizeOrderedList, SearchEngine>;
template class ExtAdd<MinimizeSubset, SearchEngine>;
template class ExtAdd<IntVarRange, SearchEngine>;
template class ExtAdd<IntVarEnum, SearchEngine>;
template class ExtAdd<CPBinaryRelVar, SearchEngine>;
template class ExtAdd<CPBinaryRel, SearchEngine>;
template class ExtAdd<CPSumWeighted, SearchEngine>;
template class ExtAdd<CPCount, SearchEngine>;
template class ExtAdd<CPAllDiff, SearchEngine>;
template class ExtAdd<Symmetry, SearchEngine>;
template class ExtAdd<LazyGroundLit, SearchEngine>;
}
