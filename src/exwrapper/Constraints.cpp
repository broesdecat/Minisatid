#include "external/Constraints.hpp"

#include "external/Remapper.hpp"
#include "external/Translator.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "external/SearchMonitor.hpp"

#include <map>
#include <vector>

using namespace std;
using namespace MinisatID;

Var MinisatID::checkAtom(const Atom& atom, Remapper& remapper) {
	return remapper.getVar(atom);
}

Lit MinisatID::checkLit(const Literal& lit, Remapper& remapper) {
	return mkLit(checkAtom(lit.getAtom(), remapper), lit.hasSign());
}

void MinisatID::checkLits(const vector<Literal>& lits, vector<Lit>& ll, Remapper& remapper) {
	ll.reserve(lits.size());
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLit(*i, remapper));
	}
}

void MinisatID::checkLits(const vector<vector<Literal> >& lits, vector<vector<Lit> >& ll, Remapper& remapper) {
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(vector<Lit>());
		checkLits(*i, ll.back(), remapper);
	}
}

void MinisatID::checkLits(const map<Literal, Literal>& lits, map<Lit, Lit>& ll, Remapper& remapper) {
	for (auto i = lits.cbegin(); i != lits.cend(); ++i) {
		ll[checkLit(i->first, remapper)] = checkLit(i->second, remapper);
	}
}

void MinisatID::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll, Remapper& remapper) {
	ll.reserve(atoms.size());
	for (auto i = atoms.cbegin(); i < atoms.cend(); ++i) {
		ll.push_back(checkAtom(*i, remapper));
	}
}

void MinisatID::checkAtoms(const std::map<Atom, Atom>& atoms, std::map<Var, Var>& ll, Remapper& remapper) {
	for (auto i = atoms.cbegin(); i != atoms.cend(); ++i) {
		ll.insert(pair<Var, Var>(checkAtom((*i).first, remapper), checkAtom((*i).second, remapper)));
	}
}
