//LICENSEPLACEHOLDER
#ifndef SATUTILS_H_
#define SATUTILS_H_

#include "GeneralUtils.hpp"

#ifdef USEMINISAT
#include "mtlold/Vec.h"
#include "mtlold/Queue.h"
#include "mtlold/Heap.h"
#include "mtlold/Sort.h"
#include "solver3minisat/SolverTypes.h"

namespace MinisatID {
	typedef Minisat::Clause& pClause;
	typedef Minisat::Clause* rClause;
	Minisat::Lit mkLit(Minisat::Var x, bool sign = false);
}

#else
	#ifdef USEMINISAT09Z
	#include "mtlold/Vec.h"
	#include "mtlold/Queue.h"
	#include "mtlold/Heap.h"
	#include "mtlold/Sort.h"
	#include "solver3/SolverTypes.hpp"

	namespace MinisatID {
		typedef Minisat::Clause& pClause;
		typedef Minisat::Clause* rClause;
		Minisat::Lit mkLit(Minisat::Var x, bool sign = false);
	}

	#else //Minisat 2.2
		#include "mtl/Vec.h"
		#include "mtl/Queue.h"
		#include "mtl/Heap.h"
		#include "mtl/Sort.h"
		#include "core/SolverTypes.h"

		namespace MinisatID {
			typedef Minisat::CRef pClause;
			typedef Minisat::CRef rClause;
			using Minisat::mkLit;
		}
	#endif
#endif

namespace MinisatID {
	using Minisat::vec;
	using Minisat::l_False;
	using Minisat::l_Undef;
	using Minisat::l_True;
	using Minisat::lbool;
	using Minisat::Var;
	using Minisat::Lit;
	using Minisat::var;
	using Minisat::toLit;
	using Minisat::toInt;

	extern rClause nullPtrClause;
	pClause getClauseRef(rClause rc);

	double getDefaultDecay();
	double getDefaultRandfreq();
	POLARITY getDefaultPolarity();
}

#endif// SATSOLVER_H_
