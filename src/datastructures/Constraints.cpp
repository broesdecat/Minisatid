/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/Constraints.hpp"

#include "space/Remapper.hpp"
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

Atom checkAtom(const Atom& atom, Remapper& remapper) {
	return remapper.getVar(atom);
}

Lit checkLit(const Lit& lit, Remapper& remapper) {
	return mkLit(checkAtom(lit.getAtom(), remapper), lit.hasSign());
}

vector<Lit> checkLits(const vector<Lit>& lits, Remapper& remapper) {
	vector<Lit> ll;
	ll.reserve(lits.size());
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLit(*i, remapper));
	}
	return ll;
}

vector<vector<Lit> > checkLits(const vector<vector<Lit> >& lits, Remapper& remapper) {
	vector<vector<Lit> > ll;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(checkLits(*i, remapper));
	}
	return ll;
}

map<Lit, Lit> checkLits(const map<Lit, Lit>& lits, Remapper& remapper) {
	map<Lit, Lit> ll;
	for (auto i = lits.cbegin(); i != lits.cend(); ++i) {
		ll[checkLit(i->first, remapper)] = checkLit(i->second, remapper);
	}
	return ll;
}

vector<Atom> checkAtoms(const vector<Atom>& atoms, Remapper& remapper) {
	vector<Atom> ll;
	ll.reserve(atoms.size());
	for (auto i = atoms.cbegin(); i < atoms.cend(); ++i) {
		ll.push_back(checkAtom(*i, remapper));
	}
	return ll;
}

std::map<Atom, Atom> checkAtoms(const std::map<Atom, Atom>& atoms, Remapper& remapper) {
	std::map<Atom, Atom> ll;
	for (auto i = atoms.cbegin(); i != atoms.cend(); ++i) {
		ll.insert( { checkAtom((*i).first, remapper), checkAtom((*i).second, remapper) });
	}
	return ll;
}

}
