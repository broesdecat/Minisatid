#ifndef BINCONSTR_HPP
#define BINCONSTR_HPP
#include <vector>
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID{

class FDAggConstraint: public Propagator{
	Lit head_;
	std::vector<IntView*> set; // TODO put weights in the view
	BinComp comp_;
	AggType const * const type;

public:
	FDAggConstraint(PCSolver* engine, IntVar* left, EqType comp, IntVar* right, Var h);

	const Lit& head() const { return head_; }

	// Propagator methods
	virtual const char* getName			() const 					{ return "fdaggconstr"; }
	virtual int		getNbOfFormulas		() const 					{ return 1; }

	virtual rClause getExplanation(const Lit& lit);

	virtual rClause	notifypropagate();

	virtual void finishParsing(bool& unsat, bool& sat);

	virtual void printState() const;
};

}

#endif //BINCONSTR_HPP
