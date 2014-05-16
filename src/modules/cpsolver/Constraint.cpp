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

TermIntVar::TermIntVar(CPScript& space, VarID groundterm, int min, int max)
		: ID(groundterm), range(false), min(min), max(max), var(space.addIntVar(min, max)) {
}

TermIntVar::TermIntVar(CPScript& space, VarID groundterm, const vector<int>& values)
		: ID(groundterm), range(false), min(-1), max(-1), values(values), var(space.addIntVar(values)) {
}

Gecode::IntVar TermIntVar::getIntVar(const CPScript& space) const {
	return space.getIntVars()[var];
}

std::vector<VarID> getID(const std::vector<TermIntVar>& vars){
	std::vector<VarID> ids;
	for(auto var:vars){
		ids.push_back(var.getID());
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

SumConstraint::SumConstraint(CPScript& space, const vector<TermIntVar>& set, const vector<int>& mult, IntRelType rel, int rhs, Atom atom)
		: ReifiedConstraint(atom, space), set(set), irhs(rhs) {
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
	for(auto val:mult){
		w.push_back(Weight(val));
	}
	visitor.add(CPSumWeighted(mkPosLit(getHead()), getID(set), w, toEqType(rel), Weight(irhs)));
}

ProdConstraint::ProdConstraint(CPScript& space, const TermIntVar& one, const TermIntVar& two, const TermIntVar& rhs, Atom atom)
		: ReifiedConstraint(atom, space), one(one), two(two), rhs(rhs) {
	mult(space, one.getIntVar(space), two.getIntVar(space), rhs.getIntVar(space) /*,consistency level*/);
}
void ProdConstraint::accept(ConstraintVisitor&) {
	throw notYetImplemented("Accept gecode-prod-constraint");
}

CountConstraint::CountConstraint(CPScript& space, const vector<TermIntVar>& set, IntRelType rel, int value, TermIntVar rhs)
		: set(set), rel(rel), eqbound(value), trhs(rhs) {
	IntVarArgs ar(set.size());
	for (uint i = 0; i < set.size(); i++) {
		ar[i] = set[i].getIntVar(space);
	}

	count(space, ar, eqbound, rel, trhs.getIntVar(space)/*,consistency level*/);
}
void CountConstraint::accept(ConstraintVisitor& visitor) {
	visitor.add(CPCount(getID(set), Weight(eqbound), toEqType(rel), trhs.getID()));
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, TermIntVar rhs, Atom atom)
		: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(false), irhs(0), trhs(rhs) {
	auto ialhs = lhs.getIntVar(space);
	auto iarhs = trhs.getIntVar(space);

	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space), ICL_DOM);
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, Atom atom)
		: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(true), irhs(rhs), trhs() {
	auto ialhs = lhs.getIntVar(space);

	Gecode::rel(space, ialhs, rel, irhs, getBoolVar(space), ICL_DOM);
}
void BinArithConstraint::accept(ConstraintVisitor& visitor) {
	if(intrhs) {
		visitor.add(CPBinaryRel(mkPosLit(getHead()), lhs.getID(), toEqType(rel), Weight(irhs)));
	} else {
		visitor.add(CPBinaryRelVar(mkPosLit(getHead()), lhs.getID(), toEqType(rel), trhs.getID()));
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

ElementConstraint::ElementConstraint(CPScript& space, const vector<TermIntVar>& set, TermIntVar index, TermIntVar rhs)
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

ostream& MinisatID::operator<<(ostream& os, const TermIntVar& tiv) {
	return os << tiv.ID.id << "[" << tiv.min << "," << tiv.max << "]";
}
