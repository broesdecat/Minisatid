/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CPSOLVERDATA_HPP_
#define CPSOLVERDATA_HPP_

#include <vector>

namespace MinisatID{
namespace CP{
	class TermIntVar;
	class ReifiedConstraint;
	class Constraint;

	typedef vector<CP::TermIntVar> vtiv;
	typedef vector<CP::ReifiedConstraint*> vreifconstrptr;
	typedef vector<CP::Constraint*> vnonrconstrptr;

	class CPSolverData{
	private:
		std::vector<CPScript*> history;
		vtiv terms;
		vnonrconstrptr nonreifconstraints;
		vreifconstrptr reifconstraints;

	public:
		CPSolverData();
		virtual ~CPSolverData();

		CPScript& 	getSpace	()	const 				{ return *history.back(); }
		CPScript& 	getPrevSpace()	const 				{ assert(history.size()>1); return *history[history.size()-2]; }

		void 		replaceLastWith	(CPScript* space);

		void 		addSpace	();
		void 		removeSpace	();

		int 		size		() 	const 				{ return history.size(); }
		CPScript const * const operator[](int i) const 	{ return history[i]; }

		const vtiv& getTerms	()	const				{ return terms; }
		void 		addTerm		(TermIntVar var)		{ terms.push_back(var);	}

		const vnonrconstrptr& 	getNonReifConstraints()	const 	{ return nonreifconstraints; }
		const vreifconstrptr& 	getReifConstraints()	const 	{ return reifconstraints; }
		//owning pointer
		void 		addReifConstraint(ReifiedConstraint* c){ reifconstraints.push_back(c); }
		void 		addNonReifConstraint(Constraint* c){ nonreifconstraints.push_back(c); }

		//vector<Lit> getBoolChanges	() const;

		TermIntVar 	convertToVar	(int term) const;
		vtiv		convertToVars	(const vector<int>& terms) const;
	};
}
}

#endif /* CPSOLVERDATA_HPP_ */
