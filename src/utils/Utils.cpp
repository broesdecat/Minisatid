/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "utils/Utils.hpp"
#include <string>
#include <sstream>

using namespace std;
using namespace MinisatID;

Var MinisatID::atom(const Lit& lit){
	return var(lit);
}

Atom MinisatID::atom(const Literal& lit){
	return lit.getAtom();
}

idpexception MinisatID::notYetImplemented(const std::string& mess){
	stringstream ss;
	ss <<"Not yet implemented: " <<mess <<"\n";
	return idpexception(ss.str());
}
