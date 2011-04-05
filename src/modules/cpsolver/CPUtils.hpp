/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CPUTILS_H
#define CPUTILS_H

#include <gecode/kernel.hh>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>

#include <utils/Utils.hpp>

namespace MinisatID{
	bool isTrue(Gecode::BoolVar var);
	bool isFalse(Gecode::BoolVar var);
	bool isAssigned(Gecode::BoolVar var);

	Gecode::IntRelType negate(Gecode::IntRelType eq);

	Gecode::IntRelType toRelType(MinisatID::EqType eq);

	std::ostream& operator<<(std::ostream& stream, Gecode::IntRelType rel);
}

#endif /*CPUTILS_H*/
