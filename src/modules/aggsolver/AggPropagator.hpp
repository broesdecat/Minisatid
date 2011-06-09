#ifndef AGGPROPAGATOR_HPP_
#define AGGPROPAGATOR_HPP_

#include "modules/DPLLTmodule.hpp"

namespace MinisatID{

class PCSolver;
class TypedSet;

class AggPropagator: public Propagator {
private:
	TypedSet* const set; //Non-owning
public:
	AggPropagator(PCSolver* s, TypedSet* set);
	virtual ~AggPropagator(){};

	virtual void 		initialize(bool& unsat, bool& sat);
	virtual rClause 	propagate		(const Lit& p, Watch* w, int level) = 0;
	virtual rClause 	propagate		(int level, const Agg& agg, bool headtrue) = 0;
	virtual rClause		propagateAtEndOfQueue(int level) = 0;
	virtual void		backtrack		(int untillevel){}
    virtual void 		getExplanation	(vec<Lit>& lits, const AggReason& ar) = 0;

    TypedSet&			getSet() 			{ return *set; }
    const TypedSet&		getSet() 	const	{ return *set; }
    TypedSet*			getSetp()	const 	{ return set; }

	//Assert: only call if model is two-valued!
	virtual Weight		getValue() const;

	rClause 			notifySolver(AggReason* ar);
};
}

#endif /* AGGPROPAGATOR_HPP_ */
