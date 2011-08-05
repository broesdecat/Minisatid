/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/BinConstr.hpp"

using namespace MinisatID;

BinaryConstraint::BinaryConstraint(PCSolver* engine, IntVar* left, EqType comp, IntVar* right, Var h): Propagator(engine), head_(mkPosLit(h)){
	switch(comp){
		case MEQ:  left_ = left; right_=right; comp_=BIN_EQ; break;
		case MNEQ: left_ = left; right_=right; comp_=BIN_NEQ; break;
		case MGEQ: left_ = right; right_=left; comp_=BIN_L; break;
		case MG:   left_ = right; right_=left; comp_=BIN_LEQ; break;
		case MLEQ: left_ = left; right_=right; comp_=BIN_LEQ; break;
		case ML:   left_ = left; right_=right; comp_=BIN_L; break;
	}
	getPCSolver().acceptBounds(left, this);
	getPCSolver().acceptBounds(right, this);
	getPCSolver().acceptLitEvent(this, head(), FAST);
	getPCSolver().acceptLitEvent(this, ~head(), FAST);
	getPCSolver().accept(this, EV_PRINTSTATE);
}

rClause BinaryConstraint::getExplanation(const Lit& lit){
	bool headtrue = getPCSolver().value(head())==l_True;
	InnerDisjunction explan;
	explan.literals.push(lit);
	if((comp_==BIN_EQ && headtrue) || (comp_==BIN_NEQ && !headtrue)){
		if(var(lit)==var(head())){ // both vars have the same value
			explan.literals.push(left()->getEQLit(left()->minValue()));
			explan.literals.push(right()->getEQLit(right()->minValue()));
		}
	}
	return getPCSolver().createClause(explan.literals, true);
	// TODO
/*		switch(comp_){
	case BIN_EQ:
		if(leftmax()<rightmin()){
			vec<Lit> clause;
			clause.push(left()->getGEQLit(rightmin()));
			clause.push(right()->getLEQLit(leftmax()));
			return getPCSolver().createClause(clause, true);
		}else if(rightmin()<leftmax()){
			vec<Lit> clause;
			clause.push(left()->getLEQLit(rightmax()));
			clause.push(right()->getGEQLit(leftmin()));
			return getPCSolver().createClause(clause, true);
		}
		propagate(left(), HIGHEREQ, rightmin());
		propagate(right(), HIGHEREQ, leftmin());
		propagate(left(), LOWEREQ, rightmax());
		propagate(right(), LOWEREQ, leftmax());
		break;
	case BIN_NEQ:
		if(satisfiedEq()){
			vec<Lit> clause;
			clause.push(left()->getNEQLit(left()->minValue()));
			clause.push(left()->getNEQLit(right()->minValue()));
			return getPCSolver().createClause(clause, true);
		}
		if(leftmin()==leftmax()){
			propagate(leftmin(), NOT, right());
		}
		break;
	case BIN_L:
		if(rightmax()<=leftmin()){
			vec<Lit> clause;
			clause.push(left()->getLEQLit(rightmax()-1));
			clause.push(right()->getLEQLit(leftmax()));
			return getPCSolver().createClause(clause, true);
		}
		propagate(left(), LOWEREQ, rightmax()-1);
		propagate(right(), HIGHEREQ, leftmin()+1);
		break;
	case BIN_LEQ:
		if(rightmax()<leftmin()){
			return getExplanation();
		}
		propagate(left(), LOWEREQ, rightmax());
		propagate(right(), HIGHEREQ, leftmin());
		break;
	}*/
}

rClause BinaryConstraint::propagate(int bound, BIN_SIGN comp, IntVar* var){
	if(comp==NOT){
		return propagate(var, NOT, bound);
	}
	return propagate(var, comp==LOWEREQ?HIGHEREQ:LOWEREQ, comp==LOWEREQ?bound+1:bound-1);
}
rClause BinaryConstraint::propagate(IntVar* var, BIN_SIGN comp, int bound){
	switch(comp){
	case LOWEREQ:
		if(bound<var->maxValue() && var->origMinValue()<=bound){
			Lit lit = var->getLEQLit(bound);
			lbool val = getPCSolver().value(lit);
			if(val==l_False){
				return getExplanation(lit);
			}else if(val==l_Undef){
				getPCSolver().setTrue(lit, this);
			}
		}
		break;
	case HIGHEREQ:
		if(var->minValue()<bound && bound<=var->origMaxValue()){
			Lit lit = var->getGEQLit(bound);
			lbool val = getPCSolver().value(lit);
			if(val==l_False){
				return getExplanation(lit);
			}else if(val==l_Undef){
				getPCSolver().setTrue(var->getGEQLit(bound), this);
			}
		}
		break;
	case NOT:{
		Lit lit = var->getNEQLit(bound);
		lbool val = getPCSolver().value(lit);
		if(val==l_False){
			return getExplanation(lit);
		}else if(val==l_Undef){
			getPCSolver().setTrue(var->getNEQLit(bound), this);
		}
		break;}
	}
	return nullPtrClause;
}

rClause	BinaryConstraint::notifypropagate(){
	rClause confl = nullPtrClause;
	lbool headvalue = getPCSolver().value(head());
	if(headvalue==l_True){
		switch(comp_){
		case BIN_EQ:
			if(confl==nullPtrClause){ confl = propagate(left(), HIGHEREQ, rightmin()); }
			if(confl==nullPtrClause){ confl = propagate(right(), HIGHEREQ, leftmin()); }
			if(confl==nullPtrClause){ confl = propagate(left(), LOWEREQ, rightmax()); }
			if(confl==nullPtrClause){ confl = propagate(right(), LOWEREQ, leftmax()); }
			break;
		case BIN_NEQ:
			if(confl==nullPtrClause){ confl = propagate(leftmin(), NOT, right()); }
			break;
		case BIN_L:
			if(confl==nullPtrClause){ confl = propagate(left(), LOWEREQ, rightmax()-1); }
			if(confl==nullPtrClause){ confl = propagate(right(), HIGHEREQ, leftmin()+1); }
			break;
		case BIN_LEQ:
			if(confl==nullPtrClause){ confl = propagate(left(), LOWEREQ, rightmax()); }
			if(confl==nullPtrClause){ confl = propagate(right(), HIGHEREQ, leftmin()); }
			break;
		}
	}else if(headvalue==l_False){
		switch(comp_){
		case BIN_EQ:
			if(confl==nullPtrClause){ confl = propagate(leftmin(), NOT, right()); }
			if(confl==nullPtrClause){ confl = propagate(rightmin(), NOT, left()); }
			break;
		case BIN_NEQ:
			if(confl==nullPtrClause){ confl = propagate(left(), HIGHEREQ, rightmin()); }
			if(confl==nullPtrClause){ confl = propagate(right(), HIGHEREQ, leftmin()); }
			if(confl==nullPtrClause){ confl = propagate(left(), LOWEREQ, rightmax()); }
			if(confl==nullPtrClause){ confl = propagate(right(), LOWEREQ, leftmax()); }
			break;
		case BIN_L: // GEQ => left()>=rightmin()
			if(confl==nullPtrClause){ confl = propagate(left(), HIGHEREQ, rightmin()); }
			if(confl==nullPtrClause){ confl = propagate(right(), LOWEREQ, leftmax()); }
			break;
		case BIN_LEQ: // G => left()>=rightmin()+1
			if(confl==nullPtrClause){ confl = propagate(left(), HIGHEREQ, rightmin()+1); }
			if(confl==nullPtrClause){ confl = propagate(right(), LOWEREQ, leftmax()-1); }
			break;
		}
	}else{ // head is unknown: can only propagate head
		bool prop = false;
		Lit headprop = head();
		switch(comp_){
		case BIN_EQ:
			if(violatedEq()){
				prop = true; headprop = ~head();
			}else if(satisfiedEq()){
				prop = true; headprop = head();
			}
			break;
		case BIN_NEQ:
			if(satisfiedEq()){
				prop = true; headprop = ~head();
			}else if(violatedEq()){
				prop = true; headprop = head();
			}
			break;
		case BIN_L:
			if(rightmax()<=leftmin()){
				prop = true; headprop = ~head();
			}else if(leftmax()<rightmax()){
				prop = true; headprop = head();
			}
			break;
		case BIN_LEQ:
			if(rightmax()<leftmin()){
				prop = true; headprop = ~head();
			}else if(leftmax()<=rightmax()){
				prop = true; headprop = head();
			}
			break;
		}
		if(prop){
			getPCSolver().setTrue(headprop, this);
		}
	}

	return confl;
}

void BinaryConstraint::printState() const{
	// TODO
}

