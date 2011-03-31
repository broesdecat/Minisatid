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

#ifndef CONSTRAINT_HPP_
#define CONSTRAINT_HPP_

#include "solvers/cpsolver/CPScript.hpp"

using namespace Gecode;

namespace CP{

	typedef vector<IntVar>::size_type termindex;
	typedef vector<BoolVar>::size_type boolindex;

	/*
	 * The mapping of an index to an interval bounded term to an ID number
	 */
	class TermIntVar{
	private:
		int ID;
		int min, max;
		termindex var;

		//	TermIntVar(TermIntVar&){}

	public:
		TermIntVar():min(-1), max(-1), var(-1){	}

		TermIntVar(CPScript& space, int groundterm, int min, int max)
			: ID(groundterm), min(min), max(max), var(space.addIntVar(min, max)){
		}

		virtual ~TermIntVar(){}

		IntVar 	getIntVar(const CPScript& space) 	const { return space.getIntVars()[var];	}

		bool 	operator==(const TermIntVar& rhs)	const { return this->operator ==(rhs.ID); }
		bool 	operator==(const int& rhs) 			const { return ID==rhs; }

		friend ostream &operator<<(ostream &stream, const TermIntVar& tiv);
	};

	class Constraint{
	public:
		Constraint(){}
		virtual ~Constraint(){}
	};

	// Represents ATOM <=> ConstraintReifiedBy(BoolVars[var])
	class ReifiedConstraint: public Constraint{
	private:
		int atom;
		boolindex var;

	public:
		ReifiedConstraint(int atom, CPScript& space);
		virtual ~ReifiedConstraint(){}

		int 	getAtom			() 						const { return atom; }
		BoolVar getBoolVar 		(const CPScript& space) const { return space.getBoolVars()[var]; }

		bool	isAssigned		(const CPScript& space) const { return CP::isAssigned(getBoolVar(space)); }
		bool	isAssignedTrue	(const CPScript& space) const { return CP::isTrue(getBoolVar(space)); }
		bool	isAssignedFalse	(const CPScript& space) const { return CP::isFalse(getBoolVar(space)); }

		rClause propagate		(bool becametrue, CPScript& space);
	};

	class SumConstraint: public ReifiedConstraint{
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

		virtual ~SumConstraint(){}
	};

	class CountConstraint: public Constraint{
	private:
		vector<TermIntVar> set;
		IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

	public:
		CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int value, TermIntVar rhs);

		virtual ~CountConstraint(){}
	};

	class BinArithConstraint: public ReifiedConstraint{
	private:
		TermIntVar lhs;
		IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

	public:
		BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, TermIntVar rhs, int atom);
		BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, int atom);

		virtual ~BinArithConstraint(){}
	};

	class DistinctConstraint: public Constraint{
	private:
		IntVarArgs set;
	public:
		//global distinct constraint
		DistinctConstraint(CPScript& space, vector<TermIntVar> tset);

		virtual ~DistinctConstraint(){}
	};

}

#endif /* CONSTRAINT_HPP_ */
