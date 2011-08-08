#ifndef BINCONSTR_HPP
#define BINCONSTR_HPP
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID{

class BinaryConstraint: public Propagator{
	Lit head_;
	IntVar *left_, *right_;
	BinComp comp_;

public:

	BinaryConstraint(PCSolver* engine, IntVar* left, EqType comp, IntVar* right, Var h);

	const Lit& head() const { return head_; }

	// Propagator methods
	virtual const char* getName			() const 					{ return "binconstr"; }
	virtual int		getNbOfFormulas		() const 					{ return 1; }

	virtual rClause getExplanation(const Lit& lit);

	IntVar* left() const { return left_;}
	IntVar* right() const { return right_;}

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

	rClause propagate(int bound, BIN_SIGN comp, IntVar* var);
	rClause propagate(IntVar* var, BIN_SIGN comp, int bound);

	virtual rClause	notifypropagate();

	virtual void printState() const;

};

}

#endif //BINCONSTR_HPP
