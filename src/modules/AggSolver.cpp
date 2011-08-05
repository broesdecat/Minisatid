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

AggSolver::AggSolver(PCSolver* s) :
		Propagator(s),
		dummyhead(-1),
		propagations(0), index(1), propindex(0),
		optimagg(NULL){
	getPCSolver().accept(this, EV_DECISIONLEVEL);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PRINTSTATE);
	getPCSolver().accept(this, EV_PRINTSTATS);
	getPCSolver().accept(this, EV_FULLASSIGNMENT);
	getPCSolver().accept(this, EV_CHOICE);
	getPCSolver().accept(this, EV_PROPAGATE);
	getPCSolver().acceptFinishParsing(this, false);
}

AggSolver::~AggSolver() {
	deleteList<TypedSet> (sets);
	deleteList<AggReason> (reasons);
	deleteList<Watch> (lit2staticwatchlist);
}

Minisat::Solver* AggSolver::getSATSolver() const{
	return getPCSolver().getSATSolver();
}

void AggSolver::adaptToNVars(uint64_t nvars){
	assert(lit2dynamicwatchlist.size() < 2*nvars);
	lit2headwatchlist.resize(2*nvars, NULL);
	lit2staticwatchlist.resize(nvars);
	var2setlist.resize(nvars);
	lit2dynamicwatchlist.resize(2 * nvars);
	reasons.resize(nvars, NULL);
	propagated.resize(nvars, LI(l_Undef, 0));
}

// WATCH MANIPULATION

void AggSolver::setHeadWatch(Lit head, Agg* agg) {
	assert(isInitializing());
	if(var(head)==dummyhead){
		if(!sign(head)){
			dummyheadtrue2watchlist.insert(agg);
		}else{
			dummyheadfalse2watchlist.insert(agg);
		}
	}else{
		assert(lit2headwatchlist[toInt(head)]==NULL);
		lit2headwatchlist[toInt(head)] = agg;
	}
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

void AggSolver::addStaticWatch(Var v, Watch* w) {
	assert(isInitializing());
	lit2staticwatchlist[v].push_back(w);
}

void AggSolver::addDynamicWatch(const Lit& l, Watch* w) {
	assert(!isParsing());
	lit2dynamicwatchlist[toInt(l)].push_back(w);
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

bool AggSolver::addSet(int setid, const vector<Lit>& lits, const vector<Weight>& weights) {
	assert(isParsing());
	assert(lits.size()>0 && lits.size()==weights.size());

	vector<WL> lw;
	for (vsize i = 0; i < lits.size(); ++i) {
#ifdef NOARBITPREC
		if(weights[i] == posInfinity() || weights[i] == negInfinity()){
			throw idpexception(
					"Weights equal to or larger than the largest integer number "
					"are not allowed in limited precision.\n");
		}
#endif
		lw.push_back(WL(lits[i], weights[i]));
	}

	TypedSet* set = new TypedSet(this, setid);
	set->setWL(lw);
	parsedSets[setid] = set;

	if (verbosity() >= 2) {
		report("Added ");
		MinisatID::print(10000, *set, true);
	}

	return true;
}

bool AggSolver::addAggrExpr(const InnerReifAggregate agg) {
	assert(isParsing());
	AggBound b(agg.sign, agg.bound);
	return addAggrExpr(agg.head, agg.setID, b, agg.type, agg.sem);
}

bool AggSolver::addAggrExpr(Var headv, int setid, const AggBound& bound, AggType type, AggSem sem){
	assert(isParsing());

	TypedSet* set = parsedSets[setid];

	// Check whether the head occurs in the body of the set, which is not allowed
	for (vsize i = 0; i < set->getWL().size(); ++i) {
		if (var(set->getWL()[i].getLit()) == headv) { //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, getPrintableVar(headv));
			throw idpexception(s);
		}
	}

	//Check that no aggregates occur with the same heads
	if (heads.find(headv) != heads.end()) {
		if(dummyhead==-1){
			clog <<">>> IMPORTANT: two aggregates with the same head occurred. Assuming that this head is certainly true.\n";
			dummyhead = headv;
			InnerDisjunction clause;
			clause.literals.push(mkLit(dummyhead, false));
			if(!getPCSolver().add(clause)){
				return false;
			}
		}else if(dummyhead!=headv){
			stringstream ss;
			ss <<"Multiple aggregates with several duplicate heads " <<getPrintableVar(dummyhead) <<" and ";
			ss <<getPrintableVar(headv) <<").\n";
			throw idpexception(ss.str());
		}
	}
	heads.insert(headv);

#ifdef DEBUG
	if(type == CARD) { //Check if all card weights are 1
		for(vwl::size_type i=0; i<parsedSets[setid]->getWL().size(); ++i) {
			if(parsedSets[setid]->getWL()[i].getWeight()!=1) {
				report("Cardinality was loaded with wrong weights");
				assert(false);
			}
		}
	}
#endif

	getPCSolver().varBumpActivity(headv);

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Agg* agg = new Agg(head, AggBound(bound),sem==DEF?COMP:sem, type);
	set->addAgg(agg);

	if (verbosity() >= 2) { //Print info on added aggregate
		MinisatID::print(verbosity(), *agg);
		report("\n");
	}

	return true;
}

void AggSolver::finishParsing(bool& present, bool& unsat) {
	assert(isParsing());
	notifyParsed();
	unsat = false;
	present = true;

	if (parsedSets.size() == 0) {
		present = false;
		notifyInitialized();
		return;
	}

	if(verbosity() >= 3){
		report("Initializing aggregates\n");
	}

	//IMPORTANT: LAZY initialization!
	adaptToNVars(nVars());

	for(mips::const_iterator i=parsedSets.begin(); i!=parsedSets.end(); ++i){
		sets.push_back((*i).second);
	}

	// Initialization of all sets

	//Rewrite completion sum and card constraints into CNF using PBSOLVER
	if(getPCSolver().modes().pbsolver && !unsat){
		unsat = !transformSumsToCNF(sets, getPCSolver());
	}

	//Finish the sets: add all body literals to the network
	vps remainingsets;
	vps satsets;
	for (vsize i=0; !unsat && i<sets.size(); ++i) {
		TypedSet* set = sets[i];
		bool setsat = false;

		if(!unsat && !setsat){
			set->initialize(unsat, setsat, sets);
		}

		if(!unsat && !setsat){
			for (vsize i = 0; i < set->getWL().size(); ++i) {
				var2setlist[var(set->getWL()[i].getLit())].push_back(set);
			}
		}

		if(setsat){
			satsets.push_back(set);
		}else{
			assert(unsat || set->getAgg().size()>0);
			remainingsets.push_back(set);
		}
	}
	sets.clear();
	sets.insert(sets.begin(), remainingsets.begin(), remainingsets.end());
	deleteList<TypedSet>(satsets);

#ifdef DEBUG
	//Check each aggregate knows it index in the set
	for(vps::const_iterator j=sets.begin(); j<sets.end(); ++j){
		for (agglist::const_iterator i = (*j)->getAgg().begin(); i<(*j)->getAgg().end(); ++i) {
			assert((*j)==(*i)->getSet());
			assert((*i)->getSet()->getAgg()[(*i)->getIndex()]==(*i));
		}
	}

	//TODO check all watches are correct
#endif

	if(unsat){
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, unsat detected.\n");
		}
		notifyInitialized();
		return;
	}

	//Gather available information
	map<AggType, int> nbaggs;
	int totalagg = 0, setlits = 0;
	for (vps::const_iterator i = sets.begin(); i < sets.end(); ++i) {
		int agg = (*i)->getAgg().size();
		totalagg += agg;
		setlits += (*i)->getWL().size();
		nbaggs[(*i)->getType().getType()]+=agg; //Defaults to 0 if new: http://forums.whirlpool.net.au/archive/1286863
	}

	if (totalagg == 0) {
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, no aggregates present after initialization.\n");
		}
		present = false;
		notifyInitialized();
		return;
	}

	//Push initial level (root, before any decisions).
	addRootLevel();
	sort(varwithheurval.rbegin(), varwithheurval.rend()); // REVERSE sort!

	printNumberOfAggregates(sets.size(), totalagg, setlits, nbaggs, verbosity());
	printState();

	notifyInitialized();
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

void AggSolver::notifyNewDecisionLevel() {
	assert(isInitialized());
	mapdecleveltotrail.push_back(littrail.size());
	setspropagatetrail.clear();
	setsbacktracktrail.push_back(vector<TypedSet*>());
}

void AggSolver::notifyBacktrack(int untillevel, const Lit& decision) {
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
	Propagator::notifyBacktrack(untillevel, decision);
}

Var	AggSolver::notifyBranchChoice(const Var& chosenvar) const {
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

rClause AggSolver::notifyFullAssignmentFound(){
	assert(isInitialized());
#ifdef DEBUG
	for(setlist::const_iterator i=sets.begin(); i<sets.end(); ++i){
		Weight w = (*i)->getProp()->getValue();
		for(agglist::const_iterator j=(*i)->getAgg().begin(); j<(*i)->getAgg().end(); ++j){
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
	}
#endif
	return nullPtrClause;
}

rClause AggSolver::doProp(){
	assert(isInitialized());
	rClause confl = nullPtrClause;

	for(; confl==nullPtrClause && propindex<littrail.size();){
		const Lit& p = littrail[propindex++];
		assert(propagated[var(p)].v==l_Undef);
		propagated[var(p)]=LI(sign(p)?l_False:l_True, index++);

		if (verbosity() >= 3) {
			report("Aggr_propagate("); print(p, l_True); report(").\n");
		}

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
rClause	AggSolver::notifypropagate(){
	assert(isInitialized());
	rClause confl = nullPtrClause;
	if (!isInitialized()) {
		return confl;
	}

	while(hasNextProp()){
		Lit l = getNextProp();
		if(var(l)<propagated.size()){ // FIXME should find a cleaner way for this!
			littrail.push_back(l);
		}
	}

	if(!modes().asapaggprop){
		confl = doProp();

		for(vector<TypedSet*>::const_iterator i=setspropagatetrail.begin(); confl==nullPtrClause && i<setspropagatetrail.end(); ++i){
			confl = (*i)->propagateAtEndOfQueue(getCurrentDecisionLevel());
		}

		printWatches(verbosity(), this, lit2dynamicwatchlist);
		setspropagatetrail.clear();
	}

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
	} else {
		ar.getAgg().getSet()->addExplanation(ar);
	}

	c = getPCSolver().createClause(ar.getClause(), true);

	//do not add each clause to SAT-solver: real slowdown for e.g. magicseries

	return c;
}

// OPTIMIZATION

//TODO do not treat optimization aggregates like normal ones!
bool AggSolver::addMnmz(Var headv, int setid, AggType type) {
	assert(isParsing());
	if (parsedSets.find(setid) == parsedSets.end()) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(headv>=0);

	TypedSet* set = parsedSets[setid];

	// Check whether the head occurs in the body of the set, which is no longer allowed
	for (vsize i = 0; i < set->getWL().size(); ++i) {
		if (var(set->getWL()[i].getLit()) == headv) { //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, getPrintableVar(headv));
			throw idpexception(s);
		}
	}

	//Check that not aggregates occur with the same heads
	for (map<int, TypedSet*>::const_iterator i = parsedSets.begin(); i != parsedSets.end(); ++i) {
		for (vsize j = 0; j < (*i).second->getAgg().size(); ++j) {
			if (var((*i).second->getAgg()[j]->getHead()) == headv) { //Exception if two agg with same head
				char s[100];
				sprintf(s, "At least two aggregates have the same head(%d).\n", getPrintableVar(headv));
				throw idpexception(s);
			}
		}
	}

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	const AggProp* prop = NULL;
	switch(type){
	case MAX:
		prop = AggProp::getMax();
		break;
	case MIN: //Minimization over a minimum aggregate cannot be transformed into minimization over a maximum aggregate
		// prop = AggProp::getMin();
		//TODO need a minimum propagator if we want to support this!
		throw idpexception("Minimization of a minimum aggregate is currently not supported.\n");
		break;
	case PROD:
		prop = AggProp::getProd();
		break;
	case SUM:
		prop = AggProp::getSum();
		break;
	case CARD:
		prop = AggProp::getCard();
		break;
	}

	Weight max = prop->getMaxPossible(set->getWL());

	Agg* ae = new Agg(head, AggBound(AGGSIGN_UB, max+1), COMP, type);
	setOptimAgg(ae);
	set->addAgg(ae);

	return true;
}

bool AggSolver::invalidateAgg(vec<Lit>& invalidation) {
	assert(isInitialized());
	Agg* a = getOptimAgg();
	TypedSet* s = a->getSet();
	AggPropagator* prop = s->getProp();
	Weight value = prop->getValue();

	getPCSolver().printCurrentOptimum(value);
	if(modes().verbosity>=1){
		clog <<"> Current optimal value " <<value <<"\n";
	}

	a->setBound(AggBound(a->getSign(), value - 1));

	if (s->getType().getMinPossible(s->getWL()) == value) {
		return true;
	}

	HeadReason ar(*a, createNegativeLiteral(var(a->getHead())));
	prop->getExplanation(invalidation, ar);

	return false;
}

/**
 * TODO: not really beautiful solution, maybe it can be fixed with ASSUMPTIONS?
 * This method has to be called after every temporary solution has been found to force the propagation of
 * the newly adapted bound.
 */
void AggSolver::propagateMnmz() {
	assert(isInitialized());
	int level = getPCSolver().getCurrentDecisionLevel();
	Agg* agg = getOptimAgg();
	TypedSet* set = agg->getSet();
	set->getProp()->propagate(level, *agg, true);
}

// PRINTING

void AggSolver::printStatistics() const {
	clog <<"> Aggregate propagations: " <<propagations <<"\n";
}

void MinisatID::printNumberOfAggregates(int nbsets, int nbagg, int nbsetlits, map<AggType, int>& nbaggs, int verbosity){
	//Print lots of information
	if (verbosity == 1) {
		clog <<"> Number of aggregates: " <<nbagg <<" aggregates over " <<nbsets <<" sets.\n";
	}else if (verbosity >= 2) {
		clog <<"> Number of minimum exprs.:     " <<nbaggs[MIN] <<".\n";
		clog <<"> Number of maximum exprs.:     " <<nbaggs[MAX] <<".\n";
		clog <<"> Number of sum exprs.:         " <<nbaggs[SUM] <<".\n";
		clog <<"> Number of product exprs.:     " <<nbaggs[PROD] <<".\n";
		clog <<"> Number of cardinality exprs.: " <<nbaggs[CARD] <<".\n";

		clog <<"> Over " <<nbsets <<" sets, aggregate set avg. size: " <<(double)nbsetlits/(double)(nbsets) <<" lits.\n";
	}
}

void AggSolver::printState() const{
	if (verbosity() >= 3) {
		clog <<"Aggregates are present after initialization:\n";
		for (vps::const_iterator i = sets.begin(); i < sets.end(); ++i) {
			for (agglist::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); ++j) {
				print(verbosity(), **j, true);
			}
		}
	}

	printWatches(verbosity(), this, lit2dynamicwatchlist);
	if (verbosity() >= 10) {
		for(agglist::const_iterator i=lit2headwatchlist.begin(); i<lit2headwatchlist.end(); ++i){
			if ((*i) != NULL) {
				clog <<"Headwatch of var " <<getPrintableVar(var((*i)->getHead())) <<": ";
				print(verbosity(), *(*i)->getSet(), true);
			}
		}
		for(set<Agg*>::const_iterator i=dummyheadfalse2watchlist.begin(); i!=dummyheadfalse2watchlist.end(); ++i){
			if ((*i) != NULL) {
				clog <<"Headwatch of var " <<getPrintableVar(var((*i)->getHead())) <<": ";
				print(verbosity(), *(*i)->getSet(), true);
			}
		}
		for(set<Agg*>::const_iterator i=dummyheadtrue2watchlist.begin(); i!=dummyheadtrue2watchlist.end(); ++i){
			if ((*i) != NULL) {
				clog <<"Headwatch of var " <<getPrintableVar(var((*i)->getHead())) <<": ";
				print(verbosity(), *(*i)->getSet(), true);
			}
		}
		Var v = 0;
		for(vvpw::const_iterator i=lit2staticwatchlist.begin(); i<lit2staticwatchlist.end(); ++i, ++v){
			if((*i).size()>0){
				Lit l = mkLit(v/2, v%2==1);
				clog <<"Bodywatches of var " <<l <<": ";
				for (vsize j = 0; j < (*i).size(); ++j) {
					clog <<"      ";
					print(verbosity(), *((*i)[j])->getSet(), true);
				}
			}
		}
		v = 0;
		for(vvpw::const_iterator i=lit2dynamicwatchlist.begin(); i<lit2dynamicwatchlist.end(); ++i, ++v){
			if((*i).size()>0){
				Lit l = mkLit(v/2, v%2==1);
				clog <<"Bodywatches of var " <<l <<": ";
				for (vsize j = 0; j < (*i).size(); ++j) {
					clog <<"      ";
					print(verbosity(), *((*i)[j])->getSet(), true);
				}
			}
		}
	}
}

/*void AggSolver::findClausalPropagations(){
 int counter = 0;
 for(vsize i=0; i<aggrminsets.size(); ++i){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrminsets[i]->getWLBegin(); j<aggrminsets[i]->getWLEnd(); ++j){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver().getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrprodsets.size(); ++i){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrprodsets[i]->getWLBegin(); j<aggrprodsets[i]->getWLEnd(); ++j){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver().getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrsumsets.size(); ++i){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrsumsets[i]->getWLBegin(); j<aggrsumsets[i]->getWLEnd(); ++j){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver().getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrmaxsets.size(); ++i){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrmaxsets[i]->getWLBegin(); j<aggrmaxsets[i]->getWLEnd(); ++j){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver().getClausesWhichOnlyContain(set).size();
 }
 reportf("Relevant clauses: %d.\n", counter);
 }*/
