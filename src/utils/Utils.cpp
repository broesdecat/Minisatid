//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

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

bool MinisatID::compareWLByWeights(const WL& one, const WL& two) {
	return one.getWeight() < two.getWeight();
}