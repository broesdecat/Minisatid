/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CONSTRAINT_HPP_
#define CONSTRAINT_HPP_

#include <vector>

#include "modules/cpsolver/CPUtils.hpp"

namespace MinisatID{
	class CPScript;

	typedef std::vector<Gecode::IntVar>::size_type termindex;
	typedef std::vector<Gecode::BoolVar>::size_type boolindex;

	// The mapping of an index to an interval bounded term to an ID number
	class TermIntVar{
	private:
		VarID ID;
		bool range;
		int min, max;
		std::vector<int> values;
		termindex var;

	public:
		TermIntVar();
		TermIntVar(CPScript& space, VarID groundterm, int min, int max);
		TermIntVar(CPScript& space, VarID groundterm, const std::vector<int>& values);

		VarID		getID	() const { return ID; }

		virtual ~TermIntVar(){}

		Gecode::IntVar 	getIntVar(const CPScript& space) 	const;

		bool 	operator==(const TermIntVar& rhs)	const { return this->operator ==(rhs.ID); }
		bool 	operator==(const VarID& rhs) 			const { return ID==rhs; }

		friend std::ostream &operator<<(std::ostream &stream, const TermIntVar& tiv);
	};

	class GecodeConstraint{
	public:
		virtual ~GecodeConstraint(){}
		virtual void accept(ConstraintVisitor& visitor) = 0;
	};

	class NonReifiedConstraint: public GecodeConstraint{

	};

	// Represents ATOM <=> ConstraintReifiedBy(BoolVars[var])
	class ReifiedConstraint: public GecodeConstraint{
	private:
		Atom head;
		boolindex var;

	public:
		ReifiedConstraint(Atom atom, CPScript& space);

		Atom 	getHead			() 						const { return head; }
		Gecode::BoolVar getBoolVar(const CPScript& space) const;

		bool	isAssigned		(const CPScript& space) const { return MinisatID::isAssigned(getBoolVar(space)); }
		bool	isAssignedTrue	(const CPScript& space) const { return MinisatID::isTrue(getBoolVar(space)); }
		bool	isAssignedFalse	(const CPScript& space) const { return MinisatID::isFalse(getBoolVar(space)); }

		rClause propagate		(bool becametrue, CPScript& space);
	};

	class SumConstraint: public ReifiedConstraint{
	private:
		std::vector<TermIntVar> set;
		Gecode::IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

		bool withmult;
		std::vector<int> mult;

	public:
		SumConstraint(CPScript& space, std::vector<TermIntVar> tset, std::vector<int> mult, Gecode::IntRelType rel, int rhs, Atom atom);

		virtual void accept(ConstraintVisitor& visitor);
	};

	class CountConstraint: public NonReifiedConstraint{
	private:
		std::vector<TermIntVar> set;
		Gecode::IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

	public:
		CountConstraint(CPScript& space, std::vector<TermIntVar> tset, Gecode::IntRelType rel, int value, TermIntVar rhs);

		virtual void accept(ConstraintVisitor& visitor);
	};

	class BinArithConstraint: public ReifiedConstraint{
	private:
		TermIntVar lhs;
		Gecode::IntRelType rel;

		bool intrhs;
		TermIntVar trhs;
		int irhs;

	public:
		BinArithConstraint(CPScript& space, TermIntVar lhs, Gecode::IntRelType rel, TermIntVar rhs, Atom atom);
		BinArithConstraint(CPScript& space, TermIntVar lhs, Gecode::IntRelType rel, int rhs, Atom atom);

		virtual void accept(ConstraintVisitor& visitor);
	};

	class DistinctConstraint: public NonReifiedConstraint{
	private:
		std::vector<TermIntVar> set;
	public:
		//global distinct constraint
		DistinctConstraint(CPScript& space, std::vector<TermIntVar> tset);

		virtual void accept(ConstraintVisitor& visitor);
	};

	class ElementConstraint: public NonReifiedConstraint{
	private:
		std::vector<TermIntVar> set;
		TermIntVar index, rhs;
	public:
		//global element constraint
		ElementConstraint(CPScript& space, std::vector<TermIntVar> tset, TermIntVar index, TermIntVar rhs);

		virtual void accept(ConstraintVisitor& visitor);
	};
}

#endif /* CONSTRAINT_HPP_ */
