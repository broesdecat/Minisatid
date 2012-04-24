/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef BINCONSTR_HPP
#define BINCONSTR_HPP
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID{

class BinaryConstraint: public Propagator{
	Lit head_;
	IntView *left_, *right_;
	BinComp comp_;

public:
	BinaryConstraint(PCSolver* engine, IntVar* left, EqType comp, IntVar* right, Var h);

	const Lit& head() const { return head_; }

	// Propagator methods
	virtual rClause getExplanation(const Lit& lit);
	virtual rClause	notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual int getNbOfFormulas() const { return (left_->maxValue()-left_->minValue())*(right_->maxValue()-right_->minValue()); }

	IntView* left() const { return left_;}
	IntView* right() const { return right_;}
	IntVar* leftvar() const { return left()->var(); }
	IntVar* rightvar() const { return right()->var(); }
	IntView* other(IntView* view) const { return left()==view?right():left(); }
	BinComp	comp() const { return comp_; }

	int leftmin() const { return left_->minValue(); }
	int leftmax() const { return left_->maxValue(); }
	int rightmin() const { return right_->minValue(); }
	int rightmax() const { return right_->maxValue(); }

	bool satisfiedEq(){
		if(leftmin()==leftmax() && rightmin()==rightmax() && leftmin()==rightmin()){
			return true;
		}
		return false;
	}

	bool violatedEq(){
		if(leftmax()<rightmin() || rightmax() < leftmin()){
			return true;
		}
		return false;
	}

	/**
	 * if lower, propagate var =< bound
	 * if ~lower, propagate var >= bound
	 */
	enum BIN_SIGN { LOWEREQ, HIGHEREQ, NOT};

	rClause propagate(int bound, BIN_SIGN comp, IntView* var);
	rClause propagate(IntView* var, BIN_SIGN comp, int bound);

//	void addExplanIntVarLit(Disjunction& clause, IntVar* othervar, int bound, AggSign varsign);
//	rClause propagate(const Lit& truehead, int bound, BIN_SIGN comp, IntVar* var, AggSign varsign);
//	rClause propagate(const Lit& truehead, IntVar* var, BIN_SIGN comp, int bound, AggSign varsign);
};

}

#endif //BINCONSTR_HPP
