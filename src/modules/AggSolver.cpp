/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/AggSolver.hpp"

#include "utils/Utils.hpp"
#include "utils/Print.hpp"

#include "modules/aggsolver/AggPrint.hpp"

#include "theorysolvers/PCSolver.hpp"

#include "modules/IDSolver.hpp"

#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include "utils/Print.hpp"

#include <algorithm>

#include "utils/IntTypes.h"
#include <cmath>

using namespace std;
using namespace MinisatID;

// WATCH MANIPULATION

void AggSolver::setHeadWatch(Lit head, Agg* agg) {
	assert(isInitializing());
	if(var(head)==dummyhead){
		if(agg->isDefined()){
			throw idpexception(getMultipleDefAggHeadsException());
		}
		if(!sign(head)){
			dummyheadtrue2watchlist.insert(agg);
		}else{
			dummyheadfalse2watchlist.insert(agg);
		}
	}else{
		assert(lit2headwatchlist[toInt(head)]==NULL);
		lit2headwatchlist[toInt(head)] = agg;
	}
	getPCSolver().acceptLitEvent(this, head, FAST);
	getPCSolver().acceptLitEvent(this, ~head, FAST);
}

void AggSolver::removeHeadWatch(Var head, int defID) {
	assert(hasIDSolver(defID));
	getIDSolver(defID).removeAggrHead(head);
	removeHeadWatch(head);
}

void AggSolver::removeHeadWatch(Var head) {
	assert(isInitializing());
	if(head==dummyhead){
		// FIXME
	}else{
		lit2headwatchlist[toInt(createNegativeLiteral(head))] = NULL;
		lit2headwatchlist[toInt(createPositiveLiteral(head))] = NULL;
	}
}

int AggSolver::getTime(Lit l) const {
	assert(!isParsing());
	int time = 0;
	if(propagated[var(l)].v!=l_Undef){
		time = propagated[var(l)].i;
	}else{
		if(value(l)!=l_Undef){
			time = index;
		}
	}
	return time;
}

void AggSolver::addRootLevel(){
	assert(isInitializing());
	setsbacktracktrail.push_back(vector<TypedSet*>());
	mapdecleveltotrail.push_back(littrail.size());
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
rClause AggSolver::notifySolver(AggReason* ar) {
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

void AggSolver::notifyNewDecisionLevel() {
	assert(isInitialized());
	mapdecleveltotrail.push_back(littrail.size());
	setspropagatetrail.clear();
	setsbacktracktrail.push_back(vector<TypedSet*>());
}

void AggSolver::notifyBacktrack(int untillevel) {
	assert(isInitialized());
	while(setsbacktracktrail.size()>(vsize)(untillevel+1)){
		for(vector<TypedSet*>::iterator j=setsbacktracktrail.back().begin(); j<setsbacktracktrail.back().end(); ++j){
			(*j)->backtrack(untillevel);
		}
		setsbacktracktrail.pop_back();
	}
	setspropagatetrail.clear();

	for(vsize i=mapdecleveltotrail[untillevel+1]; i<littrail.size(); ++i){
		propagated[var(littrail[i])]=LI(l_Undef, 0);
	}
	littrail.resize(mapdecleveltotrail[untillevel+1]);
	propindex = littrail.size();
	mapdecleveltotrail.resize(untillevel+1);
	if(littrail.size()==0){
		index = 1;
	}else{
		index = getTime(littrail.back());
	}
	Propagator::notifyBacktrack(untillevel);
}

Var	AggSolver::notifyBranchChoice(const Var& chosenvar) const{
	assert(modes().useaggheur);
	if(heurvars.find(chosenvar)!=heurvars.end()){
		for(vector<VI>::const_iterator i=varwithheurval.begin(); i<varwithheurval.end(); i++){
			if((*i).var==chosenvar){
				break;
			}else if(value((*i).var)==l_Undef){
				return (*i).var;
			}
		}
	}
	return chosenvar;
}

void AggSolver::adaptAggHeur(const vwl& wls, int nbagg){
	if(!modes().useaggheur){
		return;
	}
	int heur = 1;
	vwl wlstemp = wls;
	sort(wlstemp.begin(), wlstemp.end(), compareWLByAbsWeights); //largest numbers last
	for(vwl::const_iterator i=wlstemp.begin(); i<wlstemp.end(); i++){
		Var v = var((*i).getLit());
		set<Var>::iterator it = heurvars.find(v);
		if(it==heurvars.end()){
			heurvars.insert(v);
			for(vector<VI>::iterator j=varwithheurval.begin(); j<varwithheurval.end(); j++){
				if((*j).var == v){
					(*j).heurval += heur*nbagg;
					break;
				}
			}
		}else{
			VI vi;
			vi.var = v;
			vi.heurval = heur * nbagg;
			varwithheurval.push_back(vi);
		}
		heur++;
	}
}

rClause AggSolver::doProp(){
	assert(isInitialized());
	rClause confl = nullPtrClause;

	for(; confl==nullPtrClause && propindex<littrail.size();){
		const Lit& p = littrail[propindex++];

		if (verbosity() >= 3) {
			report("Aggr_propagate("); print(p, l_True); report(").\n");
		}
		assert(propagated[var(p)].v==l_Undef);

		propagated[var(p)]=LI(sign(p)?l_False:l_True, index++);

		Agg* pa = lit2headwatchlist[toInt(p)];
		if (pa != NULL) {
			confl = pa->getSet()->propagate(*pa, getCurrentDecisionLevel(), !sign(p));
			++propagations;

			printWatches(verbosity(), this, lit2dynamicwatchlist);
		}

		if(p==mkLit(dummyhead, false)){
			for (set<Agg*>::const_iterator i = dummyheadtrue2watchlist.begin(); confl == nullPtrClause && i != dummyheadtrue2watchlist.end(); ++i) {
				confl = (*i)->getSet()->propagate(**i, getCurrentDecisionLevel(), !sign(p));
				++propagations;
			}
		}else if(p==mkLit(dummyhead, true)){
			for (set<Agg*>::const_iterator i = dummyheadfalse2watchlist.begin(); confl == nullPtrClause && i != dummyheadfalse2watchlist.end(); ++i) {
				confl = (*i)->getSet()->propagate(**i, getCurrentDecisionLevel(), !sign(p));
				++propagations;
			}
		}

		const vector<Watch*>& ws = lit2staticwatchlist[var(p)];
		for (vector<Watch*>::const_iterator i = ws.begin(); confl == nullPtrClause && i < ws.end(); ++i) {
			confl = (*i)->getSet()->propagate(p, *i, getCurrentDecisionLevel());
			++propagations;
		}

		if (confl==nullPtrClause && lit2dynamicwatchlist[toInt(p)].size() > 0) {
			vector<Watch*> ws2(lit2dynamicwatchlist[toInt(p)]); //IMPORTANT copy: watches might be added again if no replacements are found
			lit2dynamicwatchlist[toInt(p)].clear();

			for (vector<Watch*>::const_iterator i = ws2.begin(); i < ws2.end(); ++i) {
				if (confl == nullPtrClause) {
					confl = (*i)->getSet()->propagate(p, (*i), getCurrentDecisionLevel());
					++propagations;
				} else { //If conflict found, copy all remaining watches in again
					addDynamicWatch(p, (*i));
				}
			}

			printWatches(verbosity(), this, lit2dynamicwatchlist);
		}

		if(modes().asapaggprop){
			for(vector<TypedSet*>::const_iterator i=setspropagatetrail.begin(); confl==nullPtrClause && i<setspropagatetrail.end(); ++i){
				confl = (*i)->propagateAtEndOfQueue(getCurrentDecisionLevel());
			}
			setspropagatetrail.clear();
		}
	}
	assert(confl!=nullPtrClause || propindex==littrail.size());

	return confl;
}

/**
 * Returns non-owning pointer
 */
rClause AggSolver::notifypropagate() {
	assert(isInitialized());
	rClause confl = nullPtrClause;

	while(hasNextProp()){
		const Lit& l = getNextProp();
		if(propagated.size()<var(l)+1){ //FIXME hack to prevent non-used vars to be checked
			continue;
		}
		littrail.push_back(l);
	}

	if(!modes().asapaggprop){
		//FIXME do necessary action,
		//then go to stage two and queue again
		//return confl;
	}

	confl = doProp();
	for(vector<TypedSet*>::const_iterator i=setspropagatetrail.begin(); confl==nullPtrClause && i<setspropagatetrail.end(); ++i){
		confl = (*i)->propagateAtEndOfQueue(getCurrentDecisionLevel());
	}
	printWatches(verbosity(), this, lit2dynamicwatchlist);
	setspropagatetrail.clear();

	return confl;
}

/**
 * Returns OWNING pointer. This has proven to be faster than always adding generated explanations to the
 * clause store!
 *
 * Important: verify that the clause is never constructed in and added to a different SAT-solvers!
 */
rClause AggSolver::getExplanation(const Lit& p) {
	assert(!isParsing());
	assert(reasons[var(p)] != NULL);
	AggReason& ar = *reasons[var(p)];

	rClause c = nullPtrClause;
	if (getPCSolver().modes().aggclausesaving < 2) {
		assert(ar.hasClause());

		c = getPCSolver().createClause(ar.getClause(), true);
	} else {
		ar.getAgg().getSet()->addExplanation(ar);
		c = getPCSolver().createClause(ar.getClause(), true);
	}

	//do not add each clause to SAT-solver: real slowdown for e.g. magicseries

	return c;
}
