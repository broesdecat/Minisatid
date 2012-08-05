/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/cpsolver/Constraint.hpp"

#include "modules/cpsolver/CPScript.hpp"
#include "modules/cpsolver/CPUtils.hpp"
#include "external/ConstraintVisitor.hpp"

#include "utils/Print.hpp"

using namespace std;

using namespace MinisatID;
using namespace Gecode;

TermIntVar::TermIntVar()
		: range(false), min(-1), max(-1), var(-1) {
}

TermIntVar::TermIntVar(CPScript& space, uint groundterm, int min, int max)
		: ID(groundterm), range(false), min(min), max(max), var(space.addIntVar(min, max)) {
}

TermIntVar::TermIntVar(CPScript& space, uint groundterm, const vector<int>& values)
		: ID(groundterm), range(false), min(-1), max(-1), values(values), var(space.addIntVar(values)) {
}

Gecode::IntVar TermIntVar::getIntVar(const CPScript& space) const {
	return space.getIntVars()[var];
}

std::vector<uint> getID(const std::vector<TermIntVar>& vars){
	std::vector<uint> ids;
	for(auto i=vars.cbegin(); i<vars.cend(); ++i){
		ids.push_back(i->getID());
	}
	return ids;
}

ReifiedConstraint::ReifiedConstraint(Atom atom, CPScript& space)
		: head(atom), var(space.addBoolVar()) {
}

Gecode::BoolVar ReifiedConstraint::getBoolVar(const CPScript& space) const {
	return space.getBoolVars()[var];
}

rClause ReifiedConstraint::propagate(bool becametrue, CPScript& space) {
	MAssert(!isAssigned(space));

	rel(space, getBoolVar(space), IRT_EQ, becametrue ? 1 : 0);

	return nullPtrClause;
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> set, vector<int> mult, IntRelType rel, int rhs, Atom atom)
		: ReifiedConstraint(atom, space), set(set), rel(rel), intrhs(true), irhs(rhs), withmult(true), mult(mult) {
	IntVarArgs ar(set.size());
	for (uint i = 0; i < set.size(); i++) {
		ar[i] = set[i].getIntVar(space);
	}
	IntArgs ia(mult.size());
	for (uint i = 0; i < mult.size(); i++) {
		ia[i] = mult[i];
	}

	linear(space, ia, ar, rel, irhs, getBoolVar(space)/*,consistency level*/);
}
void SumConstraint::accept(ConstraintVisitor& visitor) {
	std::vector<Weight> w;
	/*std::for_each(mult.cbegin(), mult.cend(), [&w](int x) {
	  w.push_back(Weight(x));
	});*/
	for(auto i=mult.cbegin(); i<mult.cend(); ++i){
		w.push_back(Weight(*i));
	}
	visitor.add(CPSumWeighted(getHead(), getID(set), w, toEqType(rel), Weight(irhs)));
}

CountConstraint::CountConstraint(CPScript& space, vector<TermIntVar> set, IntRelType rel, int value, TermIntVar rhs)
		: set(set), rel(rel), intrhs(false), trhs(rhs) {
	IntVarArgs ar(set.size());
	for (uint i = 0; i < set.size(); i++) {
		ar[i] = set[i].getIntVar(space);
	}

	count(space, ar, value, rel, trhs.getIntVar(space)/*,consistency level*/);
}
void CountConstraint::accept(ConstraintVisitor& visitor) {
	visitor.add(CPCount(getID(set), Weight(intrhs), toEqType(rel), trhs.getID()));
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, TermIntVar rhs, Atom atom)
		: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(false), trhs(rhs) {
	IntVar ialhs = lhs.getIntVar(space), iarhs = trhs.getIntVar(space);

	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space), ICL_DOM);
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, Atom atom)
		: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(true), irhs(rhs) {
	IntVar ialhs = lhs.getIntVar(space);
	int iarhs = irhs;

	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space), ICL_DOM);
}
void BinArithConstraint::accept(ConstraintVisitor& visitor) {
	if(intrhs) {
		visitor.add(CPBinaryRel(getHead(), lhs.getID(), toEqType(rel), Weight(irhs)));
	} else {
		visitor.add(CPBinaryRelVar(getHead(), lhs.getID(), toEqType(rel), trhs.getID()));
	}
}

DistinctConstraint::DistinctConstraint(CPScript& space, vector<TermIntVar> set)
		: set(set) {
	Gecode::IntVarArgs gset(set.size());
	for (uint i = 0; i < set.size(); i++) {
		gset[i]=set[i].getIntVar(space);
	}
	distinct(space, gset, ICL_DOM);
}
void DistinctConstraint::accept(ConstraintVisitor& visitor) {
	visitor.add(CPAllDiff(getID(set)));
}

ElementConstraint::ElementConstraint(CPScript& space, vector<TermIntVar> set, TermIntVar index, TermIntVar rhs)
		: set(set), index(index), rhs(rhs) {
	auto gindex = index.getIntVar(space);
	auto grhs = rhs.getIntVar(space);
	Gecode::IntVarArgs gset(set.size());
	for (uint i = 0; i < set.size(); i++) {
		gset[i]=set[i].getIntVar(space);
	}
	element(space, gset, gindex, grhs, ICL_DOM);
}
void ElementConstraint::accept(ConstraintVisitor& visitor) {
	visitor.add(CPElement(getID(set), index.getID(), rhs.getID()));
}

//Atmostone NON REIF
//min max abs mult NON REIF

ostream& MinisatID::operator<<(ostream& os, const TermIntVar& tiv) {
	return os << tiv.ID << "[" << tiv.min << "," << tiv.max << "]";
}
