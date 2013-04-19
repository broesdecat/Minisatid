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

Atom map(const Atom& atom, Remapper& remapper) {
	return remapper.getVar(atom);
}

VarID map(VarID var, Remapper& remapper) {
	return {remapper.getID(var.id)};
}

Lit map(const Lit& lit, Remapper& remapper) {
	return mkLit(map(lit.getAtom(), remapper), lit.hasSign());
}

vector<vector<Lit> > map(const vector<vector<Lit> >& lits, Remapper& remapper) {
	vector<vector<Lit> > ll;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ll.push_back(map(*i, remapper));
	}
	return ll;
}

std::map<Lit, Lit> map(const std::map<Lit, Lit>& lits, Remapper& remapper) {
	std::map<Lit, Lit> ll;
	for (auto i = lits.cbegin(); i != lits.cend(); ++i) {
		ll[map(i->first, remapper)] = map(i->second, remapper);
	}
	return ll;
}

std::map<Atom, Atom> map(const std::map<Atom, Atom>& atoms, Remapper& remapper) {
	std::map<Atom, Atom> ll;
	for (auto i = atoms.cbegin(); i != atoms.cend(); ++i) {
		ll.insert( { map((*i).first, remapper), map((*i).second, remapper) });
	}
	return ll;
}

}
