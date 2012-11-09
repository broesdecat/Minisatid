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

BinaryConstraint::BinaryConstraint(uint id, PCSolver* engine, IntVar* _left, EqType comp, IntVar* _right, const Lit& h)
		: Propagator(id, engine, "binary constraint") {
	switch (comp) {
	case EqType::EQ: {
		auto lefthead = mkPosLit(getPCSolver().newVar());
		auto righthead = mkPosLit(getPCSolver().newVar());
		add(Implication(getID(), h, ImplicationType::EQUIVALENT, { lefthead, righthead }, true));
		add(CPBinaryRelVar(getID(), righthead, _left->getVarID(), EqType::GEQ, _right->getVarID()));
		head_ = lefthead;
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, 0);
		break;
	}
	case EqType::NEQ: {
		auto lefthead = mkPosLit(getPCSolver().newVar());
		auto righthead = mkPosLit(getPCSolver().newVar());
		add(Implication(getID(), h, ImplicationType::EQUIVALENT, { lefthead, righthead }, false));
		add(CPBinaryRelVar(getID(), righthead, _left->getVarID(), EqType::G, _right->getVarID()));
		head_ = lefthead;
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, -1);
		break;
	}
	case EqType::LEQ:
		head_ = h;
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, 0);
		break;
	case EqType::L:
		head_ = h;
		left_ = new IntView(_left, 0);
		right_ = new IntView(_right, -1);
		break;
	case EqType::GEQ:
		head_ = h;
		left_ = new IntView(_right, 0);
		right_ = new IntView(_left, 0);
		break;
	case EqType::G:
		head_ = h;
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
	if (reason == reasons.cend()) {
		throw idpexception("Invalid code path in binconstraint getexplan.");
	}
	auto bound = reason->second.bound;
	if (var(lit) == var(head())) {
		if (lit == head()) {
			return getPCSolver().createClause(Disjunction(getID(), { lit, ~left()->getLEQLit(bound), ~right()->getGEQLit(reason->second.rightbound) }), true);
		} else { // head false
			return getPCSolver().createClause(Disjunction(getID(), { lit, ~left()->getGEQLit(bound), ~right()->getLEQLit(reason->second.rightbound) }), true);
		}
	} else {
		if (reason->second.var == left()) {
			if (reason->second.geq) { // left GEQ bound was propagated
				return getPCSolver().createClause(Disjunction(getID(), { lit, head(), ~right()->getGEQLit(bound - 1) }), true);
			} else { // left LEQ bound
				return getPCSolver().createClause(Disjunction(getID(), { lit, ~head(), ~right()->getLEQLit(bound) }), true);
			}
		} else { // right var explanation
			if (reason->second.geq) {
				return getPCSolver().createClause(Disjunction(getID(), { lit, ~head(), ~left()->getGEQLit(bound) }), true);
			} else {
				return getPCSolver().createClause(Disjunction(getID(), { lit, head(), ~left()->getLEQLit(bound + 1) }), true);
			}
		}
	}
}

void BinaryConstraint::accept(ConstraintVisitor&) {
	// FIXME
	//		which id to use
	//		what with intviews
}

rClause BinaryConstraint::notifypropagate() {
	auto headvalue = getPCSolver().value(head());
	litlist propagations;
	if (headvalue == l_True) {
		auto one = left()->getLEQLit(rightmax());
		auto lit = right()->getLEQLit(rightmax());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path.");
		}
		if (value(one) != l_True) {
			propagations.push_back(one);
			reasons[one] = BinReason(left(), false, rightmax());
		}
		auto two = right()->getGEQLit(leftmin());
		lit = left()->getGEQLit(leftmin());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path.");
		}
		if (value(two) != l_True) {
			propagations.push_back(two);
			reasons[two] = BinReason(right(), true, leftmin());
		}
	} else if (headvalue == l_False) {
		auto one = left()->getGEQLit(rightmin() + 1);
		auto lit = right()->getGEQLit(rightmin());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path.");
		}
		if (value(one) != l_True) {
			propagations.push_back(one);
			reasons[one] = BinReason(left(), true, rightmin() + 1);
		}
		auto two = right()->getLEQLit(leftmax() - 1);
		lit = left()->getLEQLit(leftmax());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path.");
		}
		if (value(two) != l_True) {
			propagations.push_back(two);
			reasons[two] = BinReason(right(), false, leftmax() - 1);
		}
	} else { // head is unknown: can only propagate head
		if (rightmax() < leftmin()) {
			auto lit = right()->getLEQLit(rightmax());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path.");
			}
			lit = left()->getGEQLit(leftmin());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path.");
			}
			propagations.push_back(~head());
			reasons[~head()] = BinReason(NULL, false, left()->minValue(), right()->maxValue());
		} else if (leftmax() <= rightmin()) {
			auto lit = right()->getGEQLit(rightmin());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path.");
			}
			lit = left()->getLEQLit(leftmax());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path.");
			}
			propagations.push_back(head());
			reasons[head()] = BinReason(NULL, false, left()->maxValue(), right()->minValue());
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

