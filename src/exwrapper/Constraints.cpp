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

vector<Lit> MinisatID::checkLits(const vector<Literal>& lits, Remapper& remapper) {
	vector<Lit> ll;
	ll.reserve(lits.size());
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLit(*i, remapper));
	}
	return ll;
}

vector<vector<Lit> > MinisatID::checkLits(const vector<vector<Literal> >& lits, Remapper& remapper) {
	vector<vector<Lit> > ll;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLits(*i, remapper));
	}
	return ll;
}

map<Lit, Lit> MinisatID::checkLits(const map<Literal, Literal>& lits, Remapper& remapper) {
	map<Lit, Lit> ll;
	for (auto i = lits.cbegin(); i != lits.cend(); ++i) {
		ll[checkLit(i->first, remapper)] = checkLit(i->second, remapper);
	}
	return ll;
}

vector<Var> MinisatID::checkAtoms(const vector<Atom>& atoms, Remapper& remapper) {
	vector<Var> ll;
	ll.reserve(atoms.size());
	for (auto i = atoms.cbegin(); i < atoms.cend(); ++i) {
		ll.push_back(checkAtom(*i, remapper));
	}
	return ll;
}

std::map<Var, Var> MinisatID::checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper) {
	std::map<Var, Var> ll;
	for (auto i = atoms.cbegin(); i != atoms.cend(); ++i) {
		ll.insert({checkAtom((*i).first, remapper), checkAtom((*i).second, remapper)});
	}
	return ll;
}
