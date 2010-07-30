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

#include "solvers/SATUtils.h"
#ifdef USEMINISAT22
using namespace Minisat;
#endif

namespace CP{
	class CPSolverData{
	private:
		vector<CPScript*> history;
		vector<TermIntVar> terms;
		vector<Constraint*> constraints;

	public:
		CPSolverData();

		~CPSolverData();

		CPScript& getSpace() const{ return *history.back(); }

		void addSpace(){
			history.push_back(static_cast<CPScript*>(getSpace().clone()));
		}

		void addSpace(CPScript* space){
			history.push_back(space);
		}

		void backtrack(){ history.pop_back(); }

		int size() const { return history.size(); }
		CPScript const * const operator[](int i) const{
			return history[i];
		}

		const vector<TermIntVar>& getTerms() const { return terms; }
		const vector<Constraint*>& getConstraints() const{ return constraints; }

		void addTerm(TermIntVar var){
			terms.push_back(var);
		}

		//owning pointer
		void addConstraint(Constraint* c){
			constraints.push_back(c);
		}

		bool allBooleansKnown() const;

		vector<Lit> getBoolChanges() const;

		TermIntVar convertToVar(int term) const;
		vector<TermIntVar> convertToVars(const vector<int>& terms) const;
	};
}

#endif /* CPSOLVERDATA_HPP_ */
