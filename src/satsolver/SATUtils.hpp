/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SATUTILS_H_
#define SATUTILS_H_

#include "external/ExternalUtils.hpp"
#include "satsolver/minisat/SolverTypes.hpp"

namespace MinisatID {
	typedef Minisat::CRef pClause;
	typedef Minisat::CRef rClause;
}

namespace MinisatID {
	using Minisat::l_False;
	using Minisat::l_Undef;
	using Minisat::l_True;
	using Minisat::lbool;

	extern rClause nullPtrClause;
	pClause getClauseRef(rClause rc);

	double getDefaultDecay();
	double getDefaultRandfreq();
	Polarity getDefaultPolarity();
}

#endif// SATSOLVER_H_
