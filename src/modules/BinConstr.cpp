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

BinaryConstraint::BinaryConstraint(PCSolver* engine, IntVar* left, EqType comp,
		IntVar* right, Var h) :
	Propagator(engine) {
	switch (comp) {
	case MEQ:	head_ = mkPosLit(h); left_ = new IntView(left, 0); right_ = new IntView(right, 0); comp_ = BIN_EQ; break;
	case MNEQ:	head_ = mkNegLit(h); left_ = new IntView(left, 0); right_ = new IntView(right, 0); comp_ = BIN_EQ; break;
	case MLEQ:	head_ = mkPosLit(h); left_ = new IntView(left, 0); right_ = new IntView(right, 0); comp_ = BIN_LEQ; break;
	case ML:	head_ = mkPosLit(h); left_ = new IntView(left, 0); right_ = new IntView(right, -1); comp_ = BIN_LEQ; break;
	case MGEQ:	head_ = mkNegLit(h); left_ = new IntView(left, 0); right_ = new IntView(right, 1); comp_ = BIN_LEQ; break;
	case MG:	head_ = mkNegLit(h); left_ = new IntView(left, 0); right_ = new IntView(right, 0); comp_ = BIN_LEQ; break;
	}
	getPCSolver().accept(this, EV_PRINTSTATE);
	getPCSolver().acceptFinishParsing(this, true); // has to be AFTER the intvars!
}

void BinaryConstraint::finishParsing(bool& unsat, bool& sat) {
	// TODO anything on intvars cannot be accepted before finishparsing of the intvar!
	getPCSolver().accept(this, head(), FAST);
	getPCSolver().accept(this, not head(), FAST);
	getPCSolver().acceptBounds(left(), this);
	getPCSolver().acceptBounds(right(), this);
}

rClause BinaryConstraint::getExplanation(const Lit& lit) {
	assert(false);
/*
	if comp is BIN_LEQ
		if lit is head
			if headtrue
				explain is left = leftmin & right = leftmin
			else if leftmax < rightmin
				explain is left =< leftmax & rightmin =< right
			else assert rightmax < leftmin
				explain is right =< rightmax & leftmin =< left
		else
			lit means var c x
			if headtrue
				assert c is LEQ
				explain is head and othervar LEQ x
			else
				assert c is NEQ
				explain is head and othervar EQ x
	else //comp is BIN_LEQ
		if lit is head
			if headtrue
				explain is left = leftmin & right = leftmin
			else if leftmax < rightmin
				explain is left =< leftmax & rightmin =< right
			else assert rightmax < leftmin
				explain is right =< rightmax & leftmin =< left
		else
			lit means var c x
			if headtrue
				assert c is LEQ
				explain is head and othervar LEQ x
			else
				assert c is NEQ
				explain is head and othervar EQ x
*/
}

rClause BinaryConstraint::propagate(int bound, BIN_SIGN comp, IntView* var) {
	if (comp == NOT) {
		return propagate(var, NOT, bound);
	}
	return propagate(var, comp == LOWEREQ ? HIGHEREQ : LOWEREQ, comp == LOWEREQ ? bound + 1 : bound - 1);
}

/**
 * Propagate the fact that var comp bound has to be true.
 * The reason for this will always contain the head and the other var!
 */
rClause BinaryConstraint::propagate(IntView* var, BIN_SIGN comp, int bound) {
	Lit othervarreason;
	Lit lit;
	switch (comp) {
	case LOWEREQ: //var <= bound
		if (bound < var->maxValue() && var->origMinValue() <= bound) {
			lit = var->getLEQLit(bound);
			othervarreason = other(var)->getLEQLit(bound);
			/*lbool val = getPCSolver().value(lit);
			if (val == l_False) {
				return getExplanation(lit);
			} else if (val == l_Undef) {
				getPCSolver().setTrue(lit, this);
			}*/
		}else{
			return nullPtrClause;
		}
		break;
	case HIGHEREQ: // var >= bound
		if (var->minValue() < bound && bound <= var->origMaxValue()) {
			lit = var->getGEQLit(bound);
			othervarreason = other(var)->getGEQLit(bound);
			/*lbool val = getPCSolver().value(lit);
			if (val == l_False) {
				return getExplanation(lit);
			} else if (val == l_Undef) {
				getPCSolver().setTrue(var->getGEQLit(bound), this);
			}*/
		}else{
			return nullPtrClause;
		}
		break;
	case NOT: {
		lit = var->getNEQLit(bound);
		othervarreason = other(var)->getEQLit(bound);
		/*lbool val = getPCSolver().value(lit);
		if (val == l_False) {
			return getExplanation(lit);
		} else if (val == l_Undef) {
			getPCSolver().setTrue(var->getNEQLit(bound), this);
		}*/
		break;
	}
	}
	Lit h = value(head())==l_True?~head():head();
	InnerDisjunction clause;
	clause.literals = { h, lit, ~othervarreason};
	const auto& ref = getPCSolver().createClause(clause, true);
	getPCSolver().addLearnedClause(ref);
	return nullPtrClause;
}

rClause BinaryConstraint::notifypropagate() {
	rClause confl = nullPtrClause;
	lbool headvalue = getPCSolver().value(head());
	if (headvalue == l_True) {
		switch (comp_) {
		case BIN_EQ:
			if (confl == nullPtrClause) {
				confl = propagate(left(), HIGHEREQ, rightmin());
			}
			if (confl == nullPtrClause) {
				confl = propagate(right(), HIGHEREQ, leftmin());
			}
			if (confl == nullPtrClause) {
				confl = propagate(left(), LOWEREQ, rightmax());
			}
			if (confl == nullPtrClause) {
				confl = propagate(right(), LOWEREQ, leftmax());
			}
			break;
		case BIN_LEQ:
			if (confl == nullPtrClause) {
				confl = propagate(left(), LOWEREQ, rightmax());
			}
			if (confl == nullPtrClause) {
				confl = propagate(right(), HIGHEREQ, leftmin());
			}
			break;
		}
	} else if (headvalue == l_False) {
		switch (comp_) {
		case BIN_EQ:
			if (confl == nullPtrClause) {
				confl = propagate(leftmin(), NOT, right());
			}
			if (confl == nullPtrClause) {
				confl = propagate(rightmin(), NOT, left());
			}
			break;
		case BIN_LEQ: // G => left()>=rightmin()+1
			if (confl == nullPtrClause) { confl = propagate(left(), HIGHEREQ, rightmin() + 1); }
			if (confl == nullPtrClause) { confl = propagate(right(), LOWEREQ, leftmax() - 1); }
			break;
		}
	} else { // head is unknown: can only propagate head
		bool prop = false;
		Lit headprop = head();
		InnerDisjunction clause;
		switch (comp_) {
		case BIN_EQ:
			if(leftmax()<rightmin()){
				clause.literals.push_back(~left()->getLEQLit(leftmax()));
				clause.literals.push_back(~right()->getGEQLit(rightmin()));
				prop = true;
				headprop = ~head();
			}else if(rightmax() < leftmin()){
				clause.literals.push_back(~left()->getGEQLit(leftmin()));
				clause.literals.push_back(~right()->getLEQLit(rightmax()));
				prop = true;
				headprop = ~head();
			}  else if (leftmin()==rightmax() && rightmin()==leftmax()) {
				clause.literals.push_back(~left()->getEQLit(leftmin()));
				clause.literals.push_back(~right()->getEQLit(rightmin()));
				prop = true;
				headprop = head();
			}
			break;
		case BIN_LEQ:
			if (rightmax() < leftmin()) {
				clause.literals.push_back(~left()->getGEQLit(leftmin()));
				clause.literals.push_back(~right()->getLEQLit(rightmax()));
				prop = true;
				headprop = ~head();
			} else if (leftmax() <= rightmin()) {
				clause.literals.push_back(~left()->getLEQLit(leftmax()));
				clause.literals.push_back(~right()->getGEQLit(rightmin()));
				prop = true;
				headprop = head();
			}
			break;
		}
		if (prop) {
			//getPCSolver().setTrue(headprop, this);
			const auto& ref = getPCSolver().createClause(clause, true);
			getPCSolver().addLearnedClause(ref);
		}
	}

	return confl;
}

void BinaryConstraint::printState() const {
	std::clog << "binConstr: " << head() << " <=> " << "var"
			<< left()->origid() << "[" << left()->minValue() << ", "
			<< left()->maxValue() << "]" << " " << comp() << " " << "var"
			<< right()->origid() << "[" << right()->minValue() << ", "
			<< right()->maxValue() << "]";
}

