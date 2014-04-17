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

BinaryConstraint::BinaryConstraint(uint id, PCSolver* engine, IntView* _left, EqType comp, IntView* _right, const Lit& h)
		: Propagator(id, engine, "binary constraint") {
	// FIXME optimize if left and right are the same variable!
	switch (comp) {
	case EqType::EQ: {
		stringstream ss;
		ss <<_left->toString() << " = " << _right->toString();
		getPCSolver().setString(h.getAtom(),ss.str());
		auto lefthead = mkPosLit(getPCSolver().newAtom());
		auto righthead = mkPosLit(getPCSolver().newAtom());
		engine->varBumpActivity(var(h));
		engine->varBumpActivity(var(h));
		engine->varBumpActivity(var(h));
		add(Implication(getID(), h, ImplicationType::EQUIVALENT, { lefthead, righthead }, true));
		add(CPBinaryRelVar(getID(), righthead, _left->getID(), EqType::GEQ, _right->getID()));
		head_ = lefthead;
		left_ = getPCSolver().getIntView(_left->getID(), 0);
		right_ = getPCSolver().getIntView(_right->getID(), 0);
		break;
	}
	case EqType::NEQ: {
		stringstream ss;
		ss <<_left->toString() << " != " << _right->toString();
		getPCSolver().setString(h.getAtom(),ss.str());
		auto lefthead = mkPosLit(getPCSolver().newAtom());
		auto righthead = mkPosLit(getPCSolver().newAtom());
		engine->varBumpActivity(var(h));
		engine->varBumpActivity(var(h));
		engine->varBumpActivity(var(h));
		add(Implication(getID(), h, ImplicationType::EQUIVALENT, { lefthead, righthead }, false));
		add(CPBinaryRelVar(getID(), righthead, _left->getID(), EqType::G, _right->getID()));
		head_ = lefthead;
		left_ = getPCSolver().getIntView(_left->getID(), 0);
		if(_right->minValue()==getMinElem<int>()){
			add(Disjunction(DEFAULTCONSTRID, {head_}));
			notifyNotPresent();
			return;
		}
		right_ = getPCSolver().getIntView(_right->getID(), -1);
		break;
	}
	case EqType::LEQ:
		head_ = h;
		left_ = getPCSolver().getIntView(_left->getID(), 0);
		right_ = getPCSolver().getIntView(_right->getID(), 0);
		break;
	case EqType::L:
		head_ = h;
		left_ = getPCSolver().getIntView(_left->getID(), 0);
		if(_right->minValue()==getMinElem<int>()){
			add(Disjunction(DEFAULTCONSTRID, {not head_}));
			notifyNotPresent();
			return;
		}
		right_ = getPCSolver().getIntView(_right->getID(), -1);
		break;
	case EqType::GEQ:
		head_ = h;
		left_ = getPCSolver().getIntView(_right->getID(), 0);
		right_ = getPCSolver().getIntView(_left->getID(), 0);
		break;
	case EqType::G:
		head_ = h;
		left_ = getPCSolver().getIntView(_right->getID(), 0);
		if(_left->minValue()==getMinElem<int>()){
			add(Disjunction(DEFAULTCONSTRID, {not head_}));
			notifyNotPresent();
			return;
		}
		right_ = getPCSolver().getIntView(_left->getID(), -1);
		break;
	}
	getPCSolver().accept(this);
	getPCSolver().accept(this, head(), FAST);
	getPCSolver().accept(this, not head(), FAST);
	getPCSolver().acceptBounds(left(), this);
	getPCSolver().acceptBounds(right(), this);
	getPCSolver().acceptForPropagation(this);

	stringstream ss;
	ss<<left()->toString() << " =< " << right()->toString();
	getPCSolver().setString(head().getAtom(), ss.str());

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
		if (reason->second.left) {
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

int BinaryConstraint::getNbOfFormulas() const {
	auto nb = ((abs(leftmax() - leftmin())) + (abs(rightmax() - rightmin()))) / 2;
	if(nb>=getMaxElem<int>()){
		return getMaxElem<int>();
	}
	return toInt(nb);
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
			throw idpexception("Invalid bin constr path A.");
		}
		if (value(one) != l_True) {
			propagations.push_back(one);
			reasons[one] = BinReason(true, false, rightmax());
		}
		auto two = right()->getGEQLit(leftmin());
		lit = left()->getGEQLit(leftmin());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path B.");
		}
		if (value(two) != l_True) {
			propagations.push_back(two);
			reasons[two] = BinReason(false, true, leftmin());
		}
	} else if (headvalue == l_False) {
		auto one = left()->getGEQLit(rightmin() + 1);
		auto lit = right()->getGEQLit(rightmin());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path C.");
		}
		if (value(one) != l_True) {
			propagations.push_back(one);
			reasons[one] = BinReason(true, true, rightmin() + 1);
		}
		auto two = right()->getLEQLit(leftmax() - 1);
		lit = left()->getLEQLit(leftmax());
		if (value(lit) != l_True) {
			throw idpexception("Invalid bin constr path D.");
		}
		if (value(two) != l_True) {
			propagations.push_back(two);
			reasons[two] = BinReason(false, false, leftmax() - 1);
		}
	} else { // head is unknown: can only propagate head
		if (rightmax() < leftmin()) {
			auto lit = right()->getLEQLit(rightmax());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path E.");
			}
			lit = left()->getGEQLit(leftmin());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path F.");
			}
			propagations.push_back(~head());
			reasons[~head()] = BinReason(false, false, left()->minValue(), right()->maxValue());
		} else if (leftmax() <= rightmin()) {
			auto lit = right()->getGEQLit(rightmin());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path G.");
			}
			lit = left()->getLEQLit(leftmax());
			if (value(lit) != l_True) {
				throw idpexception("Invalid bin constr path H.");
			}
			propagations.push_back(head());
			reasons[head()] = BinReason(false, false, left()->maxValue(), right()->minValue());
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

