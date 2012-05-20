#ifndef FD_AGG_CONSTRAINT_HPP
#define FD_AGG_CONSTRAINT_HPP
#include <vector>
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID{

// NOTE: always GEQ at the moment!
class FDAggConstraint: public Propagator{
	Lit head;
	std::vector<IntView*> vars;
	std::vector<int> weights;
	AggProp const * const type;
	int bound;

public:
	FDAggConstraint(PCSolver* engine, const Lit& head, AggType type, const std::vector<IntView*>& set, const std::vector<int>& weights, const int& bound);

	// Propagator methods
	virtual int		getNbOfFormulas		() const 					{ return 1; }
	virtual rClause getExplanation(const Lit& lit){ throw idpexception("Invalid code path.");}
	virtual rClause	notifypropagate();
	virtual void finishParsing(bool& unsat){}
};

}

#endif //FD_AGG_CONSTRAINT_HPP
