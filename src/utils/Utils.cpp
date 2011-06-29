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

using namespace std;
using namespace MinisatID;

bool MinisatID::isPositive(Lit l) {
	return !sign(l);
}
Lit MinisatID::createNegativeLiteral(Var i) {
	return mkLit(i, true);
}
Lit MinisatID::createPositiveLiteral(Var i) {
	return mkLit(i, false);
}

bool MinisatID::compareWLByLits(const WL& one, const WL& two) {
	return var(one.getLit()) < var(two.getLit());
}

bool MinisatID::compareWLByAbsWeights(const WL& one, const WL& two) {
	return abs(one.getWeight()) < abs(two.getWeight());
}
