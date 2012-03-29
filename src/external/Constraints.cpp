#include "Constraints.hpp"

#include "Remapper.hpp"
#include "external/Translator.hpp"
#include "external/SolvingMonitor.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "datastructures/InnerDataStructures.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "external/SearchMonitor.hpp"

#include <map>
#include <vector>

using namespace std;
using namespace MinisatID;

Var checkAtom(const Atom& atom, Remapper& remapper) {
	return remapper.getVar(atom);
}

Lit checkLit(const Literal& lit, Remapper& remapper) {
	return mkLit(checkAtom(lit.getAtom(), remapper), lit.hasSign());
}

void checkLits(const vector<Literal>& lits, vector<Lit>& ll, Remapper& remapper) {
	ll.reserve(lits.size());
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLit(*i, remapper));
	}
}

void checkLits(const vector<vector<Literal> >& lits, vector<vector<Lit> >& ll, Remapper& remapper) {
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(vector<Lit>());
		checkLits(*i, ll.back(), remapper);
	}
}

void checkLits(const map<Literal, Literal>& lits, map<Lit, Lit>& ll, Remapper& remapper) {
	for (auto i = lits.cbegin(); i != lits.cend(); ++i) {
		ll[checkLit(i->first, remapper)] = checkLit(i->second, remapper);
	}
}

void checkAtoms(const vector<Atom>& atoms, vector<Var>& ll, Remapper& remapper) {
	ll.reserve(atoms.size());
	for (auto i = atoms.cbegin(); i < atoms.cend(); ++i) {
		ll.push_back(checkAtom(*i, remapper));
	}
}

void checkAtoms(const std::map<Atom, Atom>& atoms, std::map<Var, Var>& ll, Remapper& remapper) {
	for (auto i = atoms.cbegin(); i != atoms.cend(); ++i) {
		ll.insert(pair<Var, Var>(checkAtom((*i).first, remapper), checkAtom((*i).second, remapper)));
	}
}

void MinisatID::add(Space& space, const Disjunction& sentence) {
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals, space.getRemapper());
	space.getEngine().add(d);
}

void MinisatID::add(Space& space, const Implication& sentence) {
	InnerImplication eq;
	eq.head = checkLit(sentence.head, space.getRemapper());
	eq.type = sentence.type;
	checkLits(sentence.body, eq.literals, space.getRemapper());
	eq.conjunctive = sentence.conjunction;
	space.getEngine().add(eq);
}

void MinisatID::add(Space& space, const Rule& sentence) {
	InnerRule rule;
	rule.head = checkAtom(sentence.head, space.getRemapper());
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body, space.getRemapper());
	space.getEngine().add(rule);
}

void MinisatID::add(Space& space, const Set& sentence) {
	WSet set;
	set.setID = sentence.setID;
	set.literals = sentence.literals;
	set.weights = vector<Weight>(sentence.literals.size(), 1);
	add(space, set);
}

void MinisatID::add(Space& space, const WSet& sentence) {
	WLSet set;
	set.setID = sentence.setID;
	for (uint i = 0; i < sentence.literals.size(); ++i) {
		set.wl.push_back(WLtuple(sentence.literals[i], sentence.weights[i]));
	}
	add(space, set);
}

void MinisatID::add(Space& space, const WLSet& sentence) {
	vector<WL> wls;
	for (auto i = sentence.wl.cbegin(); i < sentence.wl.cend(); ++i) {
		wls.push_back(WL(checkLit((*i).l, space.getRemapper()), (*i).w));
	}
	InnerWLSet set(sentence.setID, wls);
	space.getEngine().add(set);
}

void MinisatID::add(Space& space, const Aggregate& sentence) {
	InnerReifAggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head, space.getRemapper());
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	space.getEngine().add(agg);
}

void MinisatID::add(Space& space, const MinimizeSubset& sentence) {
	InnerMinimizeSubset mnm;
	checkLits(sentence.literals, mnm.literals, space.getRemapper());
	space.getEngine().add(mnm);
}

void MinisatID::add(Space& space, const MinimizeOrderedList& sentence) {
	InnerMinimizeOrderedList mnm;
	checkLits(sentence.literals, mnm.literals, space.getRemapper());
	space.getEngine().add(mnm);
}

void MinisatID::add(Space& space, const MinimizeVar& sentence) {
	InnerMinimizeVar mnm;
	mnm.varID = sentence.varID;
	space.getEngine().add(mnm);
}

void MinisatID::add(Space& space, const MinimizeAgg& sentence) {
	InnerMinimizeAgg mnm;
	mnm.setID = sentence.setid;
	mnm.type = sentence.type;
	space.getEngine().add(mnm);
}

void MinisatID::add(Space& space, const ForcedChoices& sentence) {
	InnerForcedChoices choices;
	checkLits(sentence.forcedchoices, choices.forcedchoices, space.getRemapper());
	space.getEngine().add(choices);
}

void MinisatID::add(Space& space, const Symmetry& sentence) {
	InnerSymmetry symms;
	checkLits(sentence.symmetry, symms.symmetry, space.getRemapper());
	space.getEngine().add(symms);
}

void MinisatID::add(Space& space, const LazyGroundLit& sentence) {
	InnerLazyClause lc;
	lc.monitor = sentence.monitor;
	lc.residual = checkLit(sentence.residual, space.getRemapper());
	lc.watchboth = sentence.watchboth;
	//clog <<"Watching " <<(lc.watchboth?"both":"single") <<" on " <<lc.residual <<"\n";
	space.getEngine().add(lc);
}

void MinisatID::add(Space& space, const CPIntVarEnum& sentence) {
	InnerIntVarEnum var;
	var.varID = sentence.varID;
	var.values = sentence.values;
	space.getEngine().add(var);
}
void MinisatID::add(Space& space, const CPIntVarRange& sentence) {
	InnerIntVarRange var;
	var.varID = sentence.varID;
	var.minvalue = sentence.minvalue;
	var.maxvalue = sentence.maxvalue;
	space.getEngine().add(var);
}
void MinisatID::add(Space& space, const CPBinaryRel& sentence) {
	InnerCPBinaryRel form;
	form.head = checkAtom(sentence.head, space.getRemapper());
	form.varID = sentence.varID;
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	space.getEngine().add(form);
}
void MinisatID::add(Space& space, const CPBinaryRelVar& sentence) {
	InnerCPBinaryRelVar form;
	form.head = checkAtom(sentence.head, space.getRemapper());
	form.lhsvarID = sentence.lhsvarID;
	form.rel = sentence.rel;
	form.rhsvarID = sentence.rhsvarID;
	space.getEngine().add(form);
}
void MinisatID::add(Space& space, const CPSumWeighted& sentence) {
	InnerCPSumWeighted form;
	form.head = checkAtom(sentence.head, space.getRemapper());
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	form.weights = sentence.weights;
	form.varIDs = sentence.varIDs;
	space.getEngine().add(form);
}
void MinisatID::add(Space& space, const CPCount& sentence) {
	InnerCPCount form;
	form.varIDs = sentence.varIDs;
	form.eqbound = sentence.eqbound;
	form.rel = sentence.rel;
	form.rhsvar = sentence.rhsvar;
	space.getEngine().add(form);
}
void MinisatID::add(Space& space, const CPAllDiff& sentence) {
	InnerCPAllDiff form;
	form.varIDs = sentence.varIDs;
	space.getEngine().add(form);
}
