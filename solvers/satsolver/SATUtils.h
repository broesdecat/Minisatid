//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#ifndef SATUTILS_H_
#define SATUTILS_H_

#ifdef USEMINISAT
#include "mtlold/Vec.h"
#include "mtlold/Queue.h"
#include "mtlold/Heap.h"
#include "mtlold/Sort.h"
#include "solver3minisat/SolverTypes.h"

namespace MinisatID {
	using ::vec;
	using Minisat::l_False;
	using Minisat::l_Undef;
	using Minisat::l_True;
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
		using ::vec;
		using Minisat::l_False;
		using Minisat::l_Undef;
		using Minisat::l_True;
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
			using Minisat::vec;
			typedef Minisat::CRef pClause;
			typedef Minisat::CRef rClause;
			using Minisat::mkLit;
		}
	#endif
#endif

namespace MinisatID {
	using Minisat::lbool;
	using Minisat::Var;
	using Minisat::Lit;
	using Minisat::var;
	using Minisat::toLit;
	using Minisat::toInt;

	extern rClause nullPtrClause;
	pClause getClauseRef(rClause rc);
}

#endif// SATSOLVER_H_
