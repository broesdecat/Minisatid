/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
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
