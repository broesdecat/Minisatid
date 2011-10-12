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
	virtual const char* getName			() const 					{ return "binconstr"; }
	virtual int		getNbOfFormulas		() const 					{ return 1; }

	virtual rClause getExplanation(const Lit& lit);

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

//	void addExplanIntVarLit(InnerDisjunction& clause, IntVar* othervar, int bound, AggSign varsign);
//	rClause propagate(const Lit& truehead, int bound, BIN_SIGN comp, IntVar* var, AggSign varsign);
//	rClause propagate(const Lit& truehead, IntVar* var, BIN_SIGN comp, int bound, AggSign varsign);

	virtual rClause	notifypropagate();

	virtual void finishParsing(bool& unsat, bool& sat);

	virtual void printState() const;

};

}

#endif //BINCONSTR_HPP
