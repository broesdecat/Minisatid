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

#ifndef CPSOLVERDATA_HPP_
#define CPSOLVERDATA_HPP_

#include "solvers/cpsolver/Constraint.hpp"
#include "solvers/cpsolver/CPScript.hpp"

#include "solvers/utils/Utils.hpp"
#ifdef USEMINISAT22
using namespace Minisat;
#endif

typedef vector<CP::TermIntVar> vtiv;
typedef vector<CP::ReifiedConstraint*> vreifconstrptr;
typedef vector<CP::Constraint*> vnonrconstrptr;

namespace CP{
	class CPSolverData{
	private:
		vector<CPScript*> history;
		vtiv terms;
		vnonrconstrptr nonreifconstraints;
		vreifconstrptr reifconstraints;

	public:
		CPSolverData();
		virtual ~CPSolverData();

		CPScript& 	getSpace	()	const 				{ return *history.back(); }
		void 		addSpace	()		 				{ history.push_back(static_cast<CPScript*>(getSpace().clone())); }
		void 		addSpace	(CPScript* space)		{ history.push_back(space); }
		void 		replaceLastWith	(CPScript* space);

		void 		backtrack	();

		int 		size		() 	const 				{ return history.size(); }
		CPScript const * const operator[](int i) const 	{ return history[i]; }

		const vtiv& getTerms	()	const				{ return terms; }
		void 		addTerm		(TermIntVar var)		{ terms.push_back(var);	}

		const vnonrconstrptr& 	getNonReifConstraints()	const 	{ return nonreifconstraints; }
		const vreifconstrptr& 	getReifConstraints()	const 	{ return reifconstraints; }
		//owning pointer
		void 				addReifConstraint(ReifiedConstraint* c){ reifconstraints.push_back(c); }
		void 				addNonReifConstraint(Constraint* c){ nonreifconstraints.push_back(c); }

		//vector<Lit> getBoolChanges	() const;

		TermIntVar 	convertToVar	(int term) const;
		vtiv		convertToVars	(const vector<int>& terms) const;
	};
}

#endif /* CPSOLVERDATA_HPP_ */
