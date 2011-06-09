
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

rClause AggPropagator::getExplanation(const Lit& p) {
	assert(reasons[var(p)] != NULL);
	AggReason& ar = *reasons[var(p)];

	rClause c = nullPtrClause;
	if (getPCSolver().modes().aggclausesaving < 2) {
		assert(ar.hasClause());

		c = getPCSolver().createClause(ar.getClause(), true);
	} else {
		addExplanation(ar);
		c = getPCSolver().createClause(ar.getClause(), true);
	}
	//do not add each clause to SAT-solver: real slowdown for e.g. magicseries

	return c;
}

/**
 * The method propagates the fact that p has been derived to the SAT solver. If a conflict occurs,
 * a conflict clause is returned. Otherwise, the value is set to true in the sat solver.
 *
 * @pre: literal p can be derived to be true because of the given aggregate reason
 * @remarks: only method allowed to use the sat solver datastructures
 * @returns: non-owning pointer
 *
 * INVARIANT: or the provided reason is deleted or it is IN the reason datastructure on return
 */
rClause AggPropagator::notifySolver(AggReason* ar) {
	assert(!isParsing());
	const Lit& p = ar->getPropLit();

	if(modes().bumpaggonnotify){ //seems to be better here, untested!
		//Decreases sokoban, performance, increases fastfood
		getPCSolver().varBumpActivity(var(p));
	}

	//If a propagation will be done or conflict (not already true), then add the learned clause first
	if (value(p) != l_True && getPCSolver().modes().aggclausesaving < 2) {
		//FIXME bug here if called during initialization (test with fast magicseries)
		ar->getAgg().getSet()->addExplanation(*ar);
	}

	if (value(p) == l_False) {
		if (verbosity() >= 2) {
			report("Deriving conflict in ");
			print(p, l_True);
			report(" because of the aggregate expression ");
			MinisatID::print(verbosity(), ar->getAgg(), true);
		}
		assert(getPCSolver().modes().aggclausesaving>1 || ar->hasClause());
		assert(reasons[var(p)]==NULL || getPCSolver().modes().aggclausesaving>1 || reasons[var(p)]->hasClause());

		AggReason* old_ar = reasons[var(p)];
		reasons[var(p)] = ar;
		rClause confl = getExplanation(p);	//Reason manipulation because getexplanation uses that reason!
		reasons[var(p)] = old_ar;
		delete ar; // Have to delete before addLearnedClause, as internally it might lead to backtrack and removing the reason
		getPCSolver().addLearnedClause(confl);
		return confl;
	} else if (value(p) == l_Undef) {
		if (verbosity() >= 2) {
			report("Deriving ");
			print(p, l_True);
			report(" because of the aggregate expression ");
			MinisatID::print(verbosity(), ar->getAgg(), true);
		}

		//Keeping a reason longer than necessary is not a problem => if after backtracking still unknown, then no getexplanation, if it becomes known,
		//either this is overwritten or the propagation stems from another module, which will be asked for the explanation
		if(reasons[var(p)] != NULL){
			delete reasons[var(p)];
		}
		reasons[var(p)] = ar;

		if (getPCSolver().modes().aggclausesaving < 1) {
			rClause c = getPCSolver().createClause(ar->getClause(), true);
			getPCSolver().addLearnedClause(c);
		}

		getPCSolver().setTrue(p, this);
	} else {
		delete ar;
	}
	return nullPtrClause;
}
