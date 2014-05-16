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

BinaryConstraint::BinaryConstraint(PCSolver* engine, IntView* _left, EqType comp, IntView* _right, const Lit& h)
		: Propagator(engine, "binary constraint") {
	// FIXME optimize if left and right are the same variable!
	switch (comp) {
	case EqType::EQ: {
		stringstream ss;
		ss <<_left->toString() << " = " << _right->toString();
		getPCSolver().setString(h.getAtom(),ss.str());
		auto lefthead = mkPosLit(getPCSolver().newAtom());
		auto righthead = mkPosLit(getPCSolver().newAtom());
		add(Implication(h, ImplicationType::EQUIVALENT, { lefthead, righthead }, true));
		add(CPBinaryRelVar(righthead, _left->getID(), EqType::GEQ, _right->getID()));
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
		add(Implication(h, ImplicationType::EQUIVALENT, { lefthead, righthead }, false));
		add(CPBinaryRelVar(righthead, _left->getID(), EqType::G, _right->getID()));
		head_ = lefthead;
		left_ = getPCSolver().getIntView(_left->getID(), 0);
		if(_right->minValue()==getMinElem<int>()){
			add(Disjunction({head_}));
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
			add(Disjunction({not head_}));
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
			add(Disjunction({not head_}));
			notifyNotPresent();
			return;
		}
		right_ = getPCSolver().getIntView(_left->getID(), -1);
		break;
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, head(), FAST);
	getPCSolver().accept(this, not head(), FAST);
	if(left_->isPartial()){
		add(Implication(not head(), ImplicationType::IMPLIEDBY, {left_->getNoImageLit()}, true));
		getPCSolver().accept(this, left_->getNoImageLit(), FAST);
		getPCSolver().accept(this, not left_->getNoImageLit(), FAST);
	}
	if(right_->isPartial()){
		add(Implication(not head(), ImplicationType::IMPLIEDBY, {right_->getNoImageLit()}, true));
		getPCSolver().accept(this, right_->getNoImageLit(), FAST);
		getPCSolver().accept(this, not right_->getNoImageLit(), FAST);
	}
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
	litlist lits;
	lits.push_back(lit);
	auto bound = reason->second.bound;
	if (var(lit) == var(head())) {
		if (lit == head()) {

			lits.push_back(~left()->getLEQLit(bound));
			lits.push_back(~right()->getGEQLit(reason->second.rightbound));
		} else { // head false
			lits.push_back(~left()->getGEQLit(bound));
			lits.push_back(~right()->getLEQLit(reason->second.rightbound));
		}
	} else {
		if (reason->second.left) {
			if (reason->second.geq) { // left GEQ bound was propagated
				lits.push_back(head());
				lits.push_back(~right()->getGEQLit(bound - 1));
			} else { // left LEQ bound
				lits.push_back(~head());
				lits.push_back(~right()->getLEQLit(bound));
			}
		} else { // right var explanation
			if (reason->second.geq) {
				lits.push_back(~head());
				lits.push_back(~left()->getGEQLit(bound));
			} else {
				lits.push_back(head());
				lits.push_back(~left()->getLEQLit(bound + 1));
			}
		}
	}
	lits.push_back(left()->getNoImageLit());
	lits.push_back(right()->getNoImageLit());
	return getPCSolver().createClause(Disjunction(lits), true);
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
	if(not left_->certainlyHasImage() || not right_->certainlyHasImage()){
		return nullPtrClause;
	}

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

