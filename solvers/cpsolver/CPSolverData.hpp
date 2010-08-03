/*
 * CPSolverData.hpp
 *
 *  Created on: Jul 27, 2010
 *      Author: broes
 */

#ifndef CPSOLVERDATA_HPP_
#define CPSOLVERDATA_HPP_

#include "solvers/cpsolver/Constraint.hpp"
#include "solvers/cpsolver/CPScript.hpp"

#include "solvers/utils/Utils.hpp"
#ifdef USEMINISAT22
using namespace Minisat;
#endif

typedef vector<CP::TermIntVar> vtiv;
typedef vector<CP::ReifiedConstraint*> vconstrptr;

namespace CP{
	class CPSolverData{
	private:
		vector<CPScript*> history;
		vtiv terms;
		vconstrptr constraints;

	public:
		CPSolverData();
		virtual ~CPSolverData();

		CPScript& 	getSpace	() const 			{ return *history.back(); }
		void 		addSpace	()		 			{ history.push_back(static_cast<CPScript*>(getSpace().clone())); }
		void 		addSpace	(CPScript* space)	{ history.push_back(space); }

		void 		backtrack	()					{ history.pop_back(); }

		int 		size		() const 			{ return history.size(); }
		CPScript const * const operator[](int i) const { return history[i]; }

		const vtiv& getTerms	() 			const 	{ return terms; }
		void 		addTerm		(TermIntVar var)		{ terms.push_back(var);	}

		const vconstrptr& 	getConstraints() 	const { return constraints; }
		//owning pointer
		void 				addConstraint(ReifiedConstraint* c){ constraints.push_back(c); }

		bool 		allBooleansKnown() const;
		vector<Lit> getBoolChanges	() const;

		TermIntVar 	convertToVar	(int term) const;
		vtiv		convertToVars	(const vector<int>& terms) const;
	};
}

#endif /* CPSOLVERDATA_HPP_ */
