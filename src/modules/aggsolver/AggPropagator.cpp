
#include "modules/aggsolver/AggPropagator.hpp"
#include "modules/aggsolver/AggProp.hpp"

#include "modules/DPLLTmodule.hpp"

using namespace std;
using namespace MinisatID;

AggPropagator::AggPropagator(PCSolver* s, TypedSet* set)
		:Propagator(s), set(set){
	getPCSolver().accept(this, BACKTRACK);
	getPCSolver().accept(this, CHOICE);
	getPCSolver().accept(this, DECISIONLEVEL);
	getPCSolver().acceptFinishParsing(this, false);
	getPCSolver().accept(this, PRINTSTATE);
	getPCSolver().accept(this, PRINTSTATS);

}

rClause AggPropagator::notifyFullAssignmentFound(){
#ifdef DEBUG
	Weight w = getSet().getProp()->getValue();
	for(agglist::const_iterator j=getSet().getAgg().begin(); j<getSet().getAgg().end(); ++j){
		if(verbosity()>=3){
			MinisatID::print(10, **j, true);
		}
		lbool headval = value((*j)->getHead());
		if((*j)->getSem()==IMPLICATION){
			assert((headval==l_True && isFalsified(**j, w, w)) || (headval==l_False && isSatisfied(**j, w, w)));
		}else{
			assert((headval==l_False && isFalsified(**j, w, w)) || (headval==l_True && isSatisfied(**j, w, w)));
		}
	}
#endif
	return nullPtrClause;
}

// Final initialization call!
void AggPropagator::initialize(bool& unsat, bool& sat) {
	for (agglist::const_iterator i = getSet().getAgg().begin(); i < getSet().getAgg().end(); ++i) {
		if((*i)->getSem()==IMPLICATION){
			getSolver()->setHeadWatch(~(*i)->getHead(), (*i));
		}else{
			getSolver()->setHeadWatch((*i)->getHead(), (*i));
			getSolver()->setHeadWatch(~(*i)->getHead(), (*i));
		}
	}
}

// Maximize speed of requesting values! //FIXME add to other solvers
lbool AggPropagator::value(const Lit& l) const {
	return satsolver->value(l);
}

Weight AggPropagator::getValue() const {
	Weight total = getSet().getType().getESV();
	for(vwl::const_iterator i=getSet().getWL().begin(); i<getSet().getWL().end(); ++i){
		lbool val = value((*i).getLit());
		assert(val!=l_Undef);

		if(val==l_True){
			total = getSet().getType().add(total, (*i).getWeight());
		}
	}
	return total;
}
