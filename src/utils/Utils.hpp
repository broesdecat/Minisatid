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

#ifndef UTILS_H_
#define UTILS_H_

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <map>
#include <string>

#include "satsolver/SATUtils.hpp"
#include "GeneralUtils.hpp"

typedef unsigned int uint;

namespace MinisatID {

// General vector size type usable for any POINTER types!
typedef std::vector<void*>::size_type vsize;

bool 	isPositive(Lit l);
Lit 	createNegativeLiteral(Var i);
Lit 	createPositiveLiteral(Var i);

///////
// Internal weighted literal
///////

class WL {  // Weighted literal
private:
	Lit lit;
	Weight weight;

public:
    explicit 		WL(const Lit& l, const Weight& w) : lit(l), weight(w) {}

    const Lit& 		getLit		()	const { return lit; }
    const Weight&	getWeight	()	const { return weight; }

    bool 			operator<	(const WL& p)		 const { return weight < p.weight; }
    bool 			operator<	(const Weight& bound)const { return weight < bound; }
    bool 			operator==	(const WL& p)		 const { return weight == p.weight && lit==p.lit; }
};

//Compare WLs by their literals, placing same literals next to each other
bool compareWLByLits(const WL& one, const WL& two);

//Compare WLs by their weights
bool compareWLByWeights(const WL& one, const WL& two);

}

#endif /* UTILS_H_ */
