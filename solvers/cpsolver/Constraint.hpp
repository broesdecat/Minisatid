/*
 * Constraint.hpp
 *
 *  Created on: Jul 27, 2010
 *      Author: broes
 */

#ifndef CONSTRAINT_HPP_
#define CONSTRAINT_HPP_

#include <vector>

#include <gecode/kernel.hh>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>

#include "solvers/cpsolver/CPScript.hpp"

using namespace Gecode;
using namespace std;

namespace CP{

	typedef vector<IntVar>::size_type termindex;
	typedef vector<BoolVar>::size_type boolindex;

	/**
	 * Mapping of variable-relation-value to Integer (SAT-atom)
	 *
	 * Initial loading: add ALL necessary SAT-atoms with respective mapping.
	 *
	 * Later, given a variable and (possibly reduced) domain: go over all atoms and check whether they
	 * are true-false-unknown
	 */

	class TermIntVar{
	//private:
	//	TermIntVar(TermIntVar&){}
	public:
		int term; //First element is the function symbol, subsequent ones are the arguments
		int min, max;
		termindex var;

		TermIntVar():min(-1), max(-1), var(-1){

		}

		TermIntVar(CPScript& space, int groundterm, int min, int max)
			: term(groundterm), min(min), max(max), var(space.addIntVar(min, max)){
		}

		~TermIntVar(){}

		bool operator==(const TermIntVar& rhs) const{
			return this->operator ==(rhs.term);
		}

		bool operator==(const int& rhs) const{
			return term==rhs;
		}

		friend ostream &operator<<(ostream &stream, const TermIntVar& tiv);
	};

	/*
	 * Extended propositional language:
	 * Take Constraints out of CP and into data structures!
	 * and make write(Constraint) in CP?
	 *
	 * to define intvars
	 * 		IntVar groundlit min max
	 * 			groundlit is an ID or a string or ...
	 * to restrict domain
	 *		HEAD groundlit REL int
	 * 		HEAD groundlit REL groundlit
	 * 		Set groundlit+
	 * 		Agg HEAD the same, but with REL
	 * 		...
	 * Recursive aggregates: not an issue
	 * Add our smart aggregate clause learning? Difficult, find new clause learning
	 */

	//Let this solver decide whether to use a reified representation or not

	class Constraint{
	private:
		int atom;
		boolindex var;

	public:
		Constraint(int atom, CPScript& space);

		int getAtom() const { return atom; }

		bool isAssignedTrue(const CPScript& space) const{
			return space.isTrue(getBoolVar());
		}

		bool isAssignedFalse(const CPScript& space) const{
			return space.isFalse(getBoolVar());
		}

		bool isAssigned(const CPScript& space) const{
			return space.isAssigned(getBoolVar());
		}

		void propagate(bool becametrue, CPScript& space);

		boolindex getBoolVar() const { return var; }
	};

	class SumConstraint: public Constraint{
	private:
		vector<TermIntVar> set;
		IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

		bool withmult;
		vector<int> mult;

	public:
		SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, TermIntVar rhs, int atom);

		SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int rhs, int atom);

		SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, TermIntVar rhs, int atom);

		SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, int rhs, int atom);
	};

	class CountConstraint{
	private:
		vector<TermIntVar> set;
		IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

	public:
		CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int value, TermIntVar rhs);
	};

	class BinArithConstraint: public Constraint{
	private:
		TermIntVar lhs;
		IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

	public:
		BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, TermIntVar rhs, int atom);

		BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, int atom);
	};

	class DistinctConstraint/*: public NonReifConstraint*/{
	private:
		IntVarArgs set;
	public:
		//global distinct constraint
		DistinctConstraint(CPScript& space, vector<TermIntVar> tset);
	};

}

#endif /* CONSTRAINT_HPP_ */
