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

#include "modules/cpsolver/CPUtils.hpp"

namespace MinisatID{
	class TermIntVar;
	class ReifiedConstraint;
	class Constraint;
	class CPScript;

	typedef std::vector<TermIntVar> vtiv;
	typedef std::vector<ReifiedConstraint*> reifconstrlist;
	typedef std::vector<Constraint*> vnonrconstrptr;

	class CPSolverData{
	private:
		std::vector<CPScript*> history;
		vtiv terms;
		vnonrconstrptr nonreifconstraints;
		reifconstrlist reifconstraints;

	public:
		CPSolverData();
		virtual ~CPSolverData();

		CPScript& 	getSpace	()	const 				{ return *history.back(); }
		CPScript& 	getPrevSpace()	const 				{ assert(history.size()>1); return *history[history.size()-2]; }

		void 		replaceLastWith	(CPScript* space);

		void 		addSpace	();
		void 		removeSpace	(int nblevels);

		int 		size		() 	const 				{ return history.size(); }
		const CPScript & operator[](int i) const 	{ return *history[i]; }

		const vtiv& getTerms	()	const				{ return terms; }
		void 		addTerm		(const TermIntVar& var);

		const vnonrconstrptr& 	getNonReifConstraints()	const 	{ return nonreifconstraints; }
		const reifconstrlist& 	getReifConstraints()	const 	{ return reifconstraints; }
		//owning pointer
		void 		addReifConstraint(ReifiedConstraint* c){ reifconstraints.push_back(c); }
		void 		addNonReifConstraint(Constraint* c){ nonreifconstraints.push_back(c); }

		//vector<Lit> getBoolChanges	() const;

		TermIntVar 	convertToVar	(uint term) const;
		vtiv		convertToVars	(const std::vector<uint>& terms) const;
	};
}

#endif /* CPSOLVERDATA_HPP_ */
