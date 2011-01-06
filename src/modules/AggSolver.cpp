//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
 Copyright (c) 2006-2009, Maarten Mariën

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include "modules/AggSolver.hpp"

#include "utils/Utils.hpp"
#include "utils/Print.hpp"

#include "theorysolvers/PCSolver.hpp"

#include "modules/aggsolver/AggPrint.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/aggsolver/AggTransform.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include <algorithm>

#include "utils/IntTypes.h"
#include <cmath>

using namespace std;
using namespace MinisatID;
using namespace Aggrs;

AggSolver::AggSolver(pPCSolver s) :
	DPLLTmodule(s), propagations(0) {
}

AggSolver::~AggSolver() {
	deleteList<TypedSet> (_sets);
	deleteList<AggReason> (aggreason);
	deleteList<Watch> (permwatches);
}

void AggSolver::notifyVarAdded(uint64_t nvars) {
	assert(headwatches.size() < 2*nvars);
	headwatches.resize(2*nvars, NULL);
	permwatches.resize(nvars);
	network.resize(nvars);
	tempwatches.resize(2 * nvars);
	aggreason.resize(nvars, NULL);
	propagated.resize(nvars, l_Undef);
}

void AggSolver::notifyDefinedHead(Var head){
	getPCSolver()->notifyAggrHead(head);
}

///////
// WATCH MANIPULATION
///////

void AggSolver::setHeadWatch(Lit head, Agg* agg) {
	assert(headwatches[toInt(head)]==NULL);
	headwatches[toInt(head)] = agg;
}

void AggSolver::removeHeadWatch(Var head) {
	//delete headwatches[x];
	headwatches[toInt(createNegativeLiteral(head))] = NULL;
	headwatches[toInt(createPositiveLiteral(head))] = NULL;
	getPCSolver()->removeAggrHead(head);
}

void AggSolver::addPermWatch(Var v, Watch* w) {
	permwatches[v].push_back(w);
}

void AggSolver::addTempWatch(const Lit& l, Watch* w) {
	tempwatches[toInt(l)].push_back(w);
}

///////
// MAIN OPERATIONS
///////

bool AggSolver::addSet(int setid, const vector<Lit>& lits, const vector<Weight>& weights) {
	assert(lits.size()==weights.size());

	if (lits.size() == 0) {
		char s[100];
		sprintf(s, "Set nr. %d is empty.\n", setid);
		throw idpexception(s);
	}

	if (parsedSets().find(setid) != parsedSets().end()) {
		char s[100];
		sprintf(s, "Set nr. %d is defined more than once.\n", setid);
		throw idpexception(s);
	}

	vector<WL> lw;
	for (vsize i = 0; i < lits.size(); i++) {
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
	parsedSets()[setid] = set;

	if (verbosity() >= 5) {
		report("Added ");
		Aggrs::print(verbosity(), *set, true);
	}

	return true;
}

bool AggSolver::addAggrExpr(Var headv, int setid, const Weight& bound, AggSign boundsign, AggType type, AggSem headeq) {
	AggBound b(boundsign, bound);
	return addAggrExpr(headv, setid, b, type, headeq);
}

bool AggSolver::addAggrExpr(Var headv, int setid, const AggBound& bound, AggType type, AggSem headeq){
	if (parsedSets().find(setid) == parsedSets().end()) { //Exception if does not already exist
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}
	if (headv < 0) { //Exception if head is neg
		char s[100];
		sprintf(s, "Heads have to be positive, which is violated for head %d.\n", headv);
		throw idpexception(s);
	}

	TypedSet* set = parsedSets()[setid];

	// Check whether the head occurs in the body of the set, which is not allowed
	for (vsize i = 0; i < set->getWL().size(); i++) {
		if (var(set->getWL()[i].getLit()) == headv) { //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, gprintVar(headv));
			throw idpexception(s);
		}
	}

	//Check that no aggregates occur with the same heads
	if (aggheads.find(headv) != aggheads.end()) {
		char s[100];
		sprintf(s, "At least two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}
	aggheads.insert(headv);

#ifdef DEBUG
	if(type == CARD) { //Check if all card weights are 1
		for(vwl::size_type i=0; i<parsedSets()[setid]->getWL().size(); i++) {
			if(parsedSets()[setid]->getWL()[i].getWeight()!=1) {
				report("Cardinality was loaded with wrong weights");
				assert(false);
			}
		}
	}
#endif

	getPCSolver()->varBumpActivity(headv);

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Agg* agg = new Agg(head, AggBound(bound),headeq, type);
	set->addAgg(agg);

	if (verbosity() >= 4) { //Print info on added aggregate
		Aggrs::print(verbosity(), *agg);
		report("\n");
	}

	return true;
}

void AggSolver::finishParsing(bool& present, bool& unsat) {
	unsat = false;
	present = true;

	if (parsedSets().size() == 0) {
		present = false;
		return;
	}

	if (verbosity() >= 3) {
		report("Initializing aggregates\n");
	}

	//Not used before finishparsing, so safe to initialize here!
	tempwatches.resize(2 * nVars());
	aggreason.resize(nVars(), NULL);

	for(mips::const_iterator i=parsedSets().begin(); i!=parsedSets().end(); i++){
		sets().push_back((*i).second);
	}

	// Initialization of all sets

	//Rewrite completion sum and card constraints into CNF using PBSOLVER
	if(getPCSolver()->modes().pbsolver && !unsat){
		unsat = !transformSumsToCNF(sets(), getPCSolver());
	}

	//Finish the sets: add all body literals to the network
	vps remainingsets;
	vps satsets;
	for (vsize i=0; !unsat && i<sets().size(); i++) {
		TypedSet* set = sets()[i];
		bool setsat = false;

		if(!unsat && !setsat){
			set->initialize(unsat, setsat, sets());
		}

		if(!unsat && !setsat){
			for (vsize i = 0; i < set->getWL().size(); i++) {
				network[var(set->getWL()[i].getLit())].push_back(set);
			}
		}

		if(setsat){
			satsets.push_back(set);
		}else{
			assert(unsat || set->getAgg().size()>0);
			remainingsets.push_back(set);
		}
	}
	sets().clear();
	sets().insert(sets().begin(), remainingsets.begin(), remainingsets.end());
	deleteList<TypedSet>(satsets);

#ifdef DEBUG
	for(vps::const_iterator j=sets().begin(); j<sets().end(); j++){
		for (vpagg::const_iterator i = (*j)->getAgg().begin(); i<(*j)->getAgg().end(); i++) {
			assert((*j)==(*i)->getSet());
			assert((*i)->getSet()->getAgg()[(*i)->getIndex()]==(*i));
		}
	}
#endif

	if(unsat){
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, unsat detected.\n");
		}
		return;
	}

	//Gather available information
	map<AggType, int> nbaggs;
	int totalagg = 0, setlits = 0;
	for (vps::const_iterator i = sets().begin(); i < sets().end(); i++) {
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
		return;
	}

	//Push initial level (root, before any decisions).
	backtrail.push_back(vector<TypedSet*>());
	mapdecleveltotrail.push_back(fulltrail.size());

	//Print lots of information
	if (verbosity() == 1) {
		report("> Number of aggregates: %d aggregates over %4zu sets.\n", totalagg, sets().size());
	}else if (verbosity() >= 2) {
		report("> Number of minimum exprs.:     %4d.\n", nbaggs[MIN]);
		report("> Number of maximum exprs.:     %4d.\n", nbaggs[MAX]);
		report("> Number of sum exprs.:         %4d.\n", nbaggs[SUM]);
		report("> Number of product exprs.:     %4d.\n", nbaggs[PROD]);
		report("> Number of cardinality exprs.: %4d.\n", nbaggs[CARD]);

		report("> Over %4zu sets, aggregate set avg. size: %7.2f lits.\n",
				sets().size(),(double)setlits/(double)(sets().size()));
	}

	if (verbosity() >= 3) {
		report("Aggregates are present after initialization:\n");
		for (vps::const_iterator i = sets().begin(); i < sets().end(); i++) {
			for (vpagg::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); j++) {
				Aggrs::print(verbosity(), **j, true);
			}
		}
	}

	printWatches(verbosity(), this, tempwatches);
	if (verbosity() >= 20) {
		for(vpagg::const_iterator i=headwatches.begin(); i<headwatches.end(); i++){
			if ((*i) != NULL) {
				report("Headwatch of var %d: ", gprintVar(var((*i)->getHead())));
				Aggrs::print(verbosity(), *(*i)->getSet(), true);
			}
		}
		Var v = 0;
		for(vvpw::const_iterator i=permwatches.begin(); i<permwatches.end(); i++, v++){
			if((*i).size()>0){
				report("Bodywatches of var %d: ", gprintVar(v));
				for (vsize j = 0; j < (*i).size(); j++) {
					report("      ");
					Aggrs::print(verbosity(), *((*i)[j])->getSet(), true);
				}
			}
		}
		v = 0;
		for(vvpw::const_iterator i=tempwatches.begin(); i<tempwatches.end(); i++, v++){
			if((*i).size()>0){
				report("Bodywatches of var %d: ", gprintVar(v));
				for (vsize j = 0; j < (*i).size(); j++) {
					report("      ");
					Aggrs::print(verbosity(), *((*i)[j])->getSet(), true);
				}
			}
		}
	}
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
	const Lit& p = ar->getPropLit();

	if(modes().bumpaggonnotify){
		//Decreases sokoban, performance, increases fastfood
		getPCSolver()->varBumpActivity(var(p));
	}

	//If a propagation will be done or conflict (not already true), then add the learned clause first
	if (value(p) != l_True && getPCSolver()->modes().aggclausesaving < 2) {
		vec<Lit> lits;
		lits.push(p);
		ar->getAgg().getSet()->getExplanation(lits, *ar);
		ar->setClause(lits);
	}

	if (value(p) == l_False) {
		if (verbosity() >= 2) {
			report("Deriving conflict in ");
			gprintLit(p, l_True);
			report(" because of the aggregate expression ");
			Aggrs::print(verbosity(), ar->getAgg(), true);
		}
		assert(getPCSolver()->modes().aggclausesaving>1 || ar->hasClause());
		assert(aggreason[var(p)]==NULL || getPCSolver()->modes().aggclausesaving>1 || aggreason[var(p)]->hasClause());

		AggReason* old_ar = aggreason[var(p)];
		aggreason[var(p)] = ar;
		rClause confl = getExplanation(p);	//Reason manipulation because getexplanation uses that reason!
		aggreason[var(p)] = old_ar;
		delete ar; // Have to delete before addLearnedClause, as internally it might lead to backtrack and removing the reason
		getPCSolver()->addLearnedClause(confl);
		return confl;
	} else if (value(p) == l_Undef) {
		noprops = false;
		if (verbosity() >= 2) {
			report("Deriving ");
			gprintLit(p, l_True);
			report(" because of the aggregate expression ");
			Aggrs::print(verbosity(), ar->getAgg(), true);
		}

		//Keeping a reason longer than necessary is not a problem => if after backtracking still unknown, then no getexplanation, if it becomes known,
		//either this is overwritten or the propagation stems from another module, which will be asked for the explanation
		if(aggreason[var(p)] != NULL){
			delete aggreason[var(p)];
		}
		aggreason[var(p)] = ar;

		if (getPCSolver()->modes().aggclausesaving < 1) {
			rClause c = getPCSolver()->createClause(ar->getClause(), true);
			getPCSolver()->addLearnedClause(c);
		}

		getPCSolver()->setTrue(p, this);
	} else {
		delete ar;
	}
	return nullPtrClause;
}

void AggSolver::newDecisionLevel() {
	mapdecleveltotrail.push_back(fulltrail.size());
	propstart = 0;
	proptrail.clear();
	backtrail.push_back(vector<TypedSet*>());
}

void AggSolver::backtrackDecisionLevels(int nblevels, int untillevel) {
	while(backtrail.size()>(vsize)(untillevel+1)){
		for(vector<TypedSet*>::iterator j=backtrail.back().begin(); j<backtrail.back().end(); j++){
			(*j)->backtrack(nblevels, untillevel);
		}
		backtrail.pop_back();
	}
	proptrail.clear();
	propstart = 0;

	/*report("Levels: ");
	for(int i=0; i<mapdecleveltotrail.size(); i++){
		report("%d ", mapdecleveltotrail[i]);
	}
	report("\n");
	report("Trail real:");
	for(int i=0; i<getPCSolver()->getTrail().size(); i++){
		gprintLit(getPCSolver()->getTrail()[i]);
	}
	report("\n");
	report("Trail agg: ");
	for(int i=0; i<fulltrail.size(); i++){
		gprintLit(fulltrail[i]);
	}
	report("\n");

	for(int i=0; i<propagated.size(); i++){
		report("%d(%s)", gprintVar(i), value(i)==l_True?"T":value(i)==l_False?"F":"X");
		report("%d(%s)", gprintVar(i), propagated[i]==l_True?"T":propagated[i]==l_False?"F":"X");
	}*/

	for(int i=mapdecleveltotrail[untillevel+1]; i<fulltrail.size(); i++){
		propagated[var(fulltrail[i])]=l_Undef;
	}
	fulltrail.resize(mapdecleveltotrail[untillevel+1]);
	mapdecleveltotrail.resize(untillevel+1);
}

/**
 * Returns non-owning pointer
 */
rClause AggSolver::propagate(const Lit& p) {
	if (!isInitialized()) {
		return nullPtrClause;
	}

	fulltrail.push_back(p);
	propagated[var(p)]=sign(p)?l_False:l_True;

	rClause confl = nullPtrClause;

	if (verbosity() >= 4) {
		report("Aggr_propagate("); gprintLit(p, l_True); report(").\n");
	}

	Agg* pa = headwatches[toInt(p)];
	if (pa != NULL) {
		confl = pa->getSet()->propagate(*pa, getLevel(), !sign(p));
		propagations++;

		printWatches(verbosity(), this, tempwatches);
	}

	const vector<Watch*>& ws = permwatches[var(p)];
	for (vector<Watch*>::const_iterator i = ws.begin(); confl == nullPtrClause && i < ws.end(); i++) {
		confl = (*i)->getSet()->propagate(p, *i, getLevel());
		propagations++;
	}

	if (confl==nullPtrClause && tempwatches[toInt(p)].size() > 0) {
		vector<Watch*> ws2(tempwatches[toInt(p)]); //IMPORTANT, BECAUSE WATCHES MIGHT BE ADDED AGAIN TO THE END (if no other watches are found etc)
		tempwatches[toInt(p)].clear();

		for (vector<Watch*>::const_iterator i = ws2.begin(); confl == nullPtrClause && i < ws2.end(); i++) {
			if (confl == nullPtrClause) {
				confl = (*i)->getSet()->propagate(p, (*i), getLevel());
				propagations++;
			} else { //If conflict found, copy all remaining watches in again
				addTempWatch(p, (*i));
			}
		}

		printWatches(verbosity(), this, tempwatches);
	}

	if(modes().asapaggprop){
		for(vector<TypedSet*>::const_iterator i=proptrail.begin(); confl==nullPtrClause && i<proptrail.end(); i++){
			confl = (*i)->propagateAtEndOfQueue(getLevel());
		}
		proptrail.clear();
	}

	return confl;
}

rClause	AggSolver::propagateAtEndOfQueue(){
	if (!isInitialized()) {
		return nullPtrClause;
	}

	rClause confl = nullPtrClause;

	if(!modes().asapaggprop){
		//noprops = true;
		for(vector<TypedSet*>::const_iterator i=proptrail.begin();/*+propstart; noprops && */confl==nullPtrClause && i<proptrail.end(); i++){
			confl = (*i)->propagateAtEndOfQueue(getLevel());
			//propstart++;
		}
		//if(confl!=nullPtrClause/* || noprops*/){
			proptrail.clear();
			//propstart = 0;
		//}
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
	assert(aggreason[var(p)] != NULL);
	const AggReason& ar = *aggreason[var(p)];

	rClause c = nullPtrClause;
	if (getPCSolver()->modes().aggclausesaving < 2) {
		assert(ar.hasClause());

		c = getPCSolver()->createClause(ar.getClause(), true);
	} else {
		vec<Lit> lits;
		lits.push(p);
		ar.getAgg().getSet()->getExplanation(lits, ar);

		//create a conflict clause and return it
		c = getPCSolver()->createClause(lits, true);
	}

	//do not add each clause to SAT-solver: real slowdown for e.g. magicseries

	return c;
}

///////
// RECURSIVE AGGREGATES
///////

Agg* AggSolver::getAggDefiningHead(Var v) const {
	Agg* agg = headwatches[toInt(createNegativeLiteral(v))];
	assert(agg!=NULL && agg->isDefined());
	return agg;
}

vector<Var> AggSolver::getAggHeadsWithBodyLit(Var x) const{
	vector<Var> heads;
	for (vps::const_iterator i = network[x].begin(); i < network[x].end(); i++) {
		for (vpagg::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); j++) {
			heads.push_back(var((*j)->getHead()));
		}
	}
	return heads;
}

vwl::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggDefiningHead(x)->getSet()->getWL().begin();
}

vwl::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggDefiningHead(x)->getSet()->getWL().end();
}

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		- have not been added already(seen[A]==1 for A, seen[A]==2 for ~A)
 * 		- might help to make the expression true (monotone literals!) (to make it a more relevant learned clause)
 * Currently CONSIDERABLE overapproximation: take all known false literals which are set literal or its negation,
 * do not occur in ufs and have not been seen yet.
 * Probably NEVER usable external clause!
 * TODO: optimize: add monotone literals until the aggregate can become true
 */
void AggSolver::addExternalLiterals(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, VarToJustif& seen) {
	TypedSet* set = getAggDefiningHead(v)->getSet();

	for (vwl::const_iterator i = set->getWL().begin(); i < set->getWL().end(); ++i) {
		Lit l = (*i).getLit();
		if(ufs.find(var(l)) != ufs.end() || seen[var(l)] == (isPositive(l) ? 2 : 1)){
			continue;
		}

		if(isTrue(l)){
			l = ~l;
		}

		if(!isFalse(l)){
			continue;
		}

		loopf.push(l);
		seen[var(l)] = isPositive(l) ? 2 : 1;
	}
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in heads, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, VarToJustif& currentjust) {
	for (vps::const_iterator i = network[var(w)].begin(); i < network[var(w)].end(); i++) {
		TypedSet* set = (*i);
		for (vpagg::const_iterator j = set->getAgg().begin(); j < set->getAgg().end(); j++) {
			const Agg& agg = *(*j);
			if (!agg.isDefined() || isFalse(agg.getHead())) {
				continue;
			}

			//FIXME HACK HACK!
			if(agg.getSem()==IMPLICATION && !sign(agg.getHead())){
				continue;
			}

			Var head = var(agg.getHead());
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf;
				vec<Var> nonjstf;

				if (set->getType().canJustifyHead(agg, jstf, nonjstf, currentjust, false)) {
					currentjust[head] = 0;
					heads.push(mkLit(head, false));
					jstfs.push();
					jstf.copyTo(jstfs.last());
				}
			}
		}
	}
}

/**
 * The given head is not false. So it has a (possibly looping) justification. Find this justification
 */
void AggSolver::findJustificationAggr(Var head, vec<Lit>& outjstf) {
	vec<Var> nonjstf;
	VarToJustif currentjust;
	const Agg& agg = *getAggDefiningHead(head);
	agg.getSet()->getType().canJustifyHead(agg, outjstf, nonjstf, currentjust, true);
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust) {
	const Agg& agg = *getAggDefiningHead(v);
	return agg.getSet()->getType().canJustifyHead(agg, jstf, nonjstf, currentjust, false);
}

///////
// OPTIMIZATION
///////

//TODO do not treat optimization aggregates like normal ones!
bool AggSolver::addMnmzSum(Var headv, int setid) {
	if (parsedSets().find(setid) == parsedSets().end()) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(headv>=0);

	TypedSet* set = parsedSets()[setid];

	// Check whether the head occurs in the body of the set, which is no longer allowed
	for (vsize i = 0; i < set->getWL().size(); i++) {
		if (var(set->getWL()[i].getLit()) == headv) { //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, gprintVar(headv));
			throw idpexception(s);
		}
	}

	//Check that not aggregates occur with the same heads
	for (map<int, TypedSet*>::const_iterator i = parsedSets().begin(); i != parsedSets().end(); i++) {
		for (vsize j = 0; j < (*i).second->getAgg().size(); j++) {
			if (var((*i).second->getAgg()[j]->getHead()) == headv) { //Exception if two agg with same head
				char s[100];
				sprintf(s, "At least two aggregates have the same head(%d).\n", gprintVar(headv));
				throw idpexception(s);
			}
		}
	}

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Weight max = 0;
	for (vwl::const_iterator i = set->getWL().begin(); i < set->getWL().end(); i++) {
		if ((*i).getWeight() > 0) {
			max += (*i).getWeight();
		}
	}

	Agg* ae = new Agg(head, AggBound(AGGSIGN_LB, max+1), COMP, SUM);
	ae->setOptim();
	set->addAgg(ae);

	if (verbosity() >= 3) {
		report("Added sum optimization: Optimize ");
		Aggrs::print(verbosity(), *ae);
		report("\n");
	}

	return true;
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head) {
	Agg* a = headwatches[toInt(createNegativeLiteral(head))];
	TypedSet* s = a->getSet();
	SumFWAgg* prop = dynamic_cast<SumFWAgg*> (s->getProp());

	report("Current optimum: %s\n", toString(prop->getCC()).c_str());

	a->setBound(AggBound(a->getSign(), prop->getCC() - 1));

	if (s->getBestPossible() == prop->getCC()) {
		return true;
	}

	AggReason ar(*a, BASEDONCC, createNegativeLiteral(head), true);
	prop->getExplanation(invalidation, ar);

	return false;
}

/**
 * TODO: not really beautiful solution, maybe it can be fixed with ASSUMPTIONS?
 * This method has to be called after every temporary solution has been found to force the propagation of
 * the newly adapted bound.
 */
void AggSolver::propagateMnmz(Var head) {
	int level = getPCSolver()->getCurrentDecisionLevel();
	dynamic_cast<SumFWAgg*>(headwatches[toInt(createNegativeLiteral(head))]->getSet()->getProp())->propagate(level, *headwatches[toInt(createNegativeLiteral(head))], true);
}

///////
// PRINTING
///////

void AggSolver::printStatistics() const {
	report("aggregate propagations: %-12" PRIu64 "\n", propagations);
}

void AggSolver::print(){
	Print::print(this);
}

/*void AggSolver::findClausalPropagations(){
 int counter = 0;
 for(vsize i=0; i<aggrminsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrminsets[i]->getWLBegin(); j<aggrminsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrprodsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrprodsets[i]->getWLBegin(); j<aggrprodsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrsumsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrsumsets[i]->getWLBegin(); j<aggrsumsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(vsize i=0; i<aggrmaxsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrmaxsets[i]->getWLBegin(); j<aggrmaxsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 reportf("Relevant clauses: %d.\n", counter);
 }*/
