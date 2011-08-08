/************************************
 AggSet.cpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggPrint.hpp"
#include "utils/Print.hpp"

using namespace std;

namespace MinisatID {

void TypedSet::addAgg(Agg* aggr){
	assert(aggr!=NULL);
	aggregates.push_back(aggr);
	aggr->setTypedSet(this);
	aggr->setIndex(aggregates.size()-1);
	if (getPCSolver().verbosity() >= 2) {
		MinisatID::print(getPCSolver().verbosity(), *aggr);
		report("\n");
	}
}

void TypedSet::replaceAgg(const agglist& repl){
	for(agglist::const_iterator i=aggregates.begin(); i<aggregates.end(); ++i){
		assert((*i)->getSet()==this);
		(*i)->setTypedSet(NULL);
		(*i)->setIndex(-1);
	}
	aggregates.clear();
	for(agglist::const_iterator i=repl.begin(); i<repl.end(); ++i){
		addAgg(*i);
	}
}

void TypedSet::replaceAgg(const agglist& repl, const agglist& del){
	replaceAgg(repl);
	for(agglist::const_iterator i=del.begin(); i<del.end(); ++i){
		delete *i;
	}
}

void TypedSet::finishParsing(bool& present, bool& unsat){
	assert(isParsing());
	notifyParsed();
	unsat = false;
	present = true;

	if(not unsat && present){
		if (verbosity() >= 2) {
			report("Added ");
			MinisatID::print(10000, *this, true);
		}

		bool sat = not present;
		for(auto i=transformations.begin(); present && not unsat && i<transformations.end(); ++i) {
			AggTransformation* transfo = *i;
			transformations.erase(i); i--;
			transfo->transform(pcsolver, this, unsat, sat);
		}

		if(not sat && not unsat){
			setProp(getType().createPropagator(this));
			prop->initialize(unsat, sat);
		}

		present = not sat;
	}

	if(present){
		assert(unsat || getAgg().size()>0);
	}

#ifdef DEBUG
	//Check each aggregate knows it index in the set
	for (agglist::const_iterator i = getAgg().begin(); i<getAgg().end(); ++i) {
		assert(this==(*i)->getSet());
		assert(getAgg()[(*i)->getIndex()]==(*i));
	}

	//TODO check all watches are correct
#endif

	if(unsat){
		if (verbosity() >= 3) {
			report("Initializing aggregate set, unsat detected.\n");
		}
		notifyInitialized();
		return;
	}

	//Push initial level (root, before any decisions).
	littrail.newDecisionLevel();

	notifyInitialized();
}

rClause TypedSet::notifySolver(AggReason* ar) {
	assert(!isParsing());
	const Lit& p = ar->getPropLit();

	if(modes().bumpaggonnotify){ //seems to be better here, untested!
		//Decreases sokoban and dansmee performance, increases fastfood
		getPCSolver().varBumpActivity(var(p));
	}

	//If a propagation will be done or conflict (not already true), then add the learned clause first
	if (value(p) != l_True && getPCSolver().modes().aggclausesaving < 2) {
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

void TypedSet::addExplanation(AggReason& ar) const {
	vec<Lit> lits;
	lits.push(ar.getPropLit());
	getProp()->getExplanation(lits, ar);
	ar.setClause(lits);

	if(verbosity()>=3){
		std::clog <<"Explanation for deriving " <<ar.getPropLit();
		std::clog <<" in expression ";
		print(verbosity(), ar.getAgg(), false);
		std::clog <<" is ";
		for(int i=0; i<lits.size(); ++i){
			std::clog <<" " <<lits[i];
		}
		std::clog <<"\n";
	}
}

void TypedSet::notifyNewDecisionLevel(){
	littrail.newDecisionLevel();
}
rClause	TypedSet::notifypropagate(){
	while(littrail.hasNext()){
		// TODO propagate all literals
	}
	getProp()->propagateAtEndOfQueue();
}

void TypedSet::notifyBacktrack(int untillevel, const Lit& decision){
	getProp()->backtrack(untillevel);
	littrail.backtrackDecisionLevels(untillevel);
	Propagator::notifyBacktrack(untillevel, decision);
}

rClause TypedSet::notifyFullAssignmentFound(){
	assert(isInitialized());
#ifdef DEBUG
	Weight w = getProp()->getValue();
	for(agglist::const_iterator j=getAgg().begin(); j<getAgg().end(); ++j){
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

//Returns OWNING pointer. This has proven to be faster than always adding generated explanations to the clause store!
rClause TypedSet::getExplanation(const Lit& p) {
	assert(!isParsing());

	assert(reasons[var(p)] != NULL);
	AggReason& ar = *reasons[var(p)];

	rClause c = nullPtrClause;
	if (getPCSolver().modes().aggclausesaving < 2) {
		assert(ar.hasClause());
	} else {
		ar.getAgg().getSet()->addExplanation(ar);
	}

	c = getPCSolver().createClause(ar.getClause(), true);

	//do not add each clause to SAT-solver: real slowdown for e.g. magicseries

	return c;
}

int	TypedSet::getNbOfFormulas() const {
	return getAgg().size() * getWL().size() * log(getWL().size()); // Could refine depending on aggregate type
}

} /* namespace MinisatID */
