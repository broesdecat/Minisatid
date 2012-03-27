/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef WL_HPP_
#define WL_HPP_

#include "external/Weight.hpp"

namespace MinisatID{
// Internal weighted literal

class WL {
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

typedef std::vector<WL> vwl;

//Compare WLs by their literals, placing same literals next to each other
bool compareWLByLits(const WL& one, const WL& two);

//Compare WLs by their weights
template<class T>
bool compareByWeights(const T& one, const T& two) {
      return one.getWeight() < two.getWeight();
}

bool compareWLByAbsWeights(const WL& one, const WL& two);

}

#endif /* WL_HPP_ */
