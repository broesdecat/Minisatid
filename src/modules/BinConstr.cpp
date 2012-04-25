/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/BinConstr.hpp"
#include <iostream>
#include "utils/Print.hpp"

using namespace MinisatID;
using namespace std;

BinaryConstraint::BinaryConstraint(PCSolver* engine, IntVar* _left, EqType comp, IntVar* _right, Var h)
		: Propagator(engine, "binary constraint") {
	switch (comp) {
	case EqType::EQ: {
		auto lefthead = getPCSolver().newVar();
		auto righthead = getPCSolver().newVar();
		internalAdd(Implication(mkPosLit(h), ImplicationType::EQUIVALENT, { mkPosLit(lefthead), mkPosLit(righthead) }, true), getPCSolver());
		internalAdd(CPBinaryRelVar(righthead, _left->origid(), EqType::GEQ, _right->origid()), getPCSolver());
		head_ = mkPosLit(lefthead);
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, 0);
		break;
	}
	case EqType::NEQ: {
		auto lefthead = getPCSolver().newVar();
		auto righthead = getPCSolver().newVar();
		internalAdd(Implication(mkPosLit(h), ImplicationType::EQUIVALENT, { mkPosLit(lefthead), mkPosLit(righthead) }, false), getPCSolver());
		internalAdd(CPBinaryRelVar(righthead, _left->origid(), EqType::G, _right->origid()), getPCSolver());
		head_ = mkPosLit(lefthead);
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, -1);
		break;
	}
	case EqType::LEQ:
		head_ = mkPosLit(h);
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, 0);
		break;
	case EqType::L:
		head_ = mkPosLit(h);
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, -1);
		break;
	case EqType::GEQ:
		head_ = mkPosLit(h);
		left_ = new IntView(_right, 0);
		right_ = new IntView(_left, 0);
		break;
	case EqType::G:
		head_ = mkPosLit(h);
		left_ = new IntView(_right, 0);
		right_ = new IntView(_left, -1);
		break;
	}
	getPCSolver().accept(this);
	getPCSolver().accept(this, head(), FAST);
	getPCSolver().accept(this, not head(), FAST);
	getPCSolver().acceptBounds(left(), this);
	getPCSolver().acceptBounds(right(), this);

	if (verbosity() > 5) {
		clog << "Binconstr: " << toString(head()) << " <=> " << left()->toString() << " =< " << right()->toString() << "\n";
	}
}

rClause BinaryConstraint::getExplanation(const Lit& lit) {
	auto reason = reasons.find(lit);
	MAssert(reason!=reasons.cend());
	if (var(lit) == var(head())) {
		if (lit == head()) {
			return getPCSolver().createClause(Disjunction( { lit, ~left()->getLEQLit(reason->second.bound), ~right()->getGEQLit(reason->second.bound) }), true);
		} else { // head false
			return getPCSolver().createClause(Disjunction( { lit, ~left()->getGEQLit(reason->second.bound), ~right()->getLEQLit(reason->second.bound - 1) }),
					true);
		}
	} else {
		if (reason->second.var == left()) {
			if (reason->second.geq) { // left GEQ bound was propagated
				return getPCSolver().createClause(Disjunction( { lit, head(), ~right()->getGEQLit(reason->second.bound - 1) }), true);
			} else { // left LEQ bound
				return getPCSolver().createClause(Disjunction( { lit, ~head(), ~right()->getLEQLit(reason->second.bound) }), true);
			}
		} else { // right var explanation
			if (reason->second.geq) {
				return getPCSolver().createClause(Disjunction( { lit, ~head(), ~left()->getGEQLit(reason->second.bound) }), true);
			} else {
				return getPCSolver().createClause(Disjunction( { lit, head(), ~left()->getLEQLit(reason->second.bound + 1) }), true);
			}
		}
	}
}

void BinaryConstraint::accept(ConstraintVisitor& visitor) {
	// FIXME
	//		which id to use
	//		what with intviews
}

rClause BinaryConstraint::notifypropagate() {
	auto headvalue = getPCSolver().value(head());
	litlist propagations;
	if (headvalue == l_True) {
		auto one = left()->getLEQLit(rightmax());
		MAssert(value(right()->getLEQLit(rightmax()))==l_True);
		if (value(one) != l_True) {
			propagations.push_back(one);
			reasons[one] = BinReason(left(), false, rightmax());
		}
		auto two = right()->getGEQLit(leftmin());
		MAssert(value(left()->getGEQLit(leftmin()))==l_True);
		if (value(two) != l_True) {
			propagations.push_back(two);
			reasons[two] = BinReason(right(), true, leftmin());
		}
	} else if (headvalue == l_False) {
		auto one = left()->getGEQLit(rightmin() + 1);
		MAssert(value(right()->getGEQLit(rightmin()+1))==l_True);
		if (value(one) != l_True) {
			propagations.push_back(one);
			reasons[one] = BinReason(left(), true, rightmin() + 1);
		}
		auto two = right()->getLEQLit(leftmax() - 1);
		MAssert(value(left()->getLEQLit(leftmax()-1))==l_True);
		if (value(two) != l_True) {
			propagations.push_back(two);
			reasons[two] = BinReason(right(), false, leftmax() - 1);
		}
	} else { // head is unknown: can only propagate head
		if (rightmax() < leftmin()) {
			MAssert(value(right()->getLEQLit(rightmax()))==l_True);
			MAssert(value(left()->getGEQLit(leftmin()))==l_True);
			propagations.push_back(~head());
			reasons[~head()] = BinReason(NULL, false, left()->minValue());
		} else if (leftmax() <= rightmin()) {
			MAssert(value(right()->getGEQLit(rightmin()))==l_True);
			MAssert(value(left()->getLEQLit(leftmax()))==l_True);
			propagations.push_back(head());
			reasons[head()] = BinReason(NULL, false, left()->maxValue());
		}
	}

	auto confl = nullPtrClause;
	for (auto i = propagations.cbegin(); i < propagations.cend() && confl == nullPtrClause; ++i) {
		auto val = value(*i);
		if (val == l_False) {
			confl = getExplanation(*i);
		} else if (val == l_Undef) {
			getPCSolver().setTrue(*i, this);
		}
	}
	return confl;
}

/*void BinaryConstraint::printState() const {
 std::clog << "binConstr: " << print(head(), getPCSolver()) << " <=> " << "var"
 << left()->origid() << "[" << left()->minValue() << ", "
 << left()->maxValue() << "]" << " " << comp() << " " << "var"
 << right()->origid() << "[" << right()->minValue() << ", "
 << right()->maxValue() << "]";
 }*/

