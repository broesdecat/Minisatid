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

#include "GeneralUtils.hpp"

#ifdef USEMINISAT
#include "minisat2-14/SolverTypes.hpp"

namespace MinisatID {
	typedef Minisat::Clause& pClause;
	typedef Minisat::Clause* rClause;
	Minisat::Lit mkLit(Minisat::Var x, bool sign = false);
}

#else
	#ifdef USEMINISAT09Z
	#include "minisat2-14-hack2009/SolverTypes.hpp"

	namespace MinisatID {
		typedef Minisat::Clause& pClause;
		typedef Minisat::Clause* rClause;
		Minisat::Lit mkLit(Minisat::Var x, bool sign = false);
	}

	#else //Minisat 2.2
		#include "core/SolverTypes.h"

		namespace MinisatID {
			typedef Minisat::CRef pClause;
			typedef Minisat::CRef rClause;
			using Minisat::mkLit;
		}
	#endif
#endif

namespace MinisatID {
	using Minisat::l_False;
	using Minisat::l_Undef;
	using Minisat::l_True;
	using Minisat::lbool;
	using Minisat::Var;
	using Minisat::Lit;
	using Minisat::var;

	extern rClause nullPtrClause;
	pClause getClauseRef(rClause rc);

	double getDefaultDecay();
	double getDefaultRandfreq();
	POLARITY getDefaultPolarity();
}

#endif// SATSOLVER_H_
