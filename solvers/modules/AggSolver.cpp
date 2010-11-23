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

#include "modules/aggsolver/AggComb.hpp"

#include "modules/aggsolver/FullyWatched.hpp"
#include "modules/aggsolver/PartiallyWatched.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>
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
	assert(headwatches.size() < nvars);
	headwatches.resize(nvars, NULL);
	permwatches.resize(nvars);
	network.resize(nvars);

	if (isInitialized()) {
		//only used after initialization, such that we can safely initialize them later!
		tempwatches.resize(2 * nvars);
		aggreason.resize(nvars, NULL);
	}
}

void AggSolver::notifyDefinedHead(Var head){
	getPCSolver()->notifyAggrHead(head);
}

///////
// WATCH MANIPULATION
///////

void AggSolver::setHeadWatch(Var head, Agg* agg) {
	headwatches[head] = agg;
}

void AggSolver::removeHeadWatch(Var x) {
	//delete headwatches[x];
	headwatches[x] = NULL;
	getPCSolver()->removeAggrHead(x);
}

void AggSolver::addPermWatch(Var v, Watch* w) {
	permwatches[v].push_back(w);
}

void AggSolver::addTempWatch(const Lit& l, Watch* w) {
	tempwatches[toInt(l)].push_back(w);
}

inline Agg* AggSolver::getAggWithHead(Var v) const {
	assert(headwatches[v] != NULL);
	return headwatches[v];
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
#ifdef INTWEIGHT
		if (weights[i] == INT_MAX || weights[i] == INT_MIN) {
			throw idpexception("Weights equal to or larger than the largest integer number "
				"are not allowed in limited precision.\n");
		}
#endif
		lw.push_back(WL(lits[i], weights[i]));

		// Literals occurring in aggregates would occur much more often in clauses, so we bump them (a bit)
		//getPCSolver()->varBumpActivity(var(lits[i]));
	}

	TypedSet* set = new TypedSet(this, setid);
	set->setWL(lw);
	parsedSets()[setid] = set;

	if (verbosity() >= 5) { // Print information on added set
		report("Added set %d: ", setid);
		vector<Weight>::const_iterator w = weights.begin();
		bool begin = true;
		for (vsize i = 0; i < lits.size(); i++, w++) {
			if (begin) {
				begin = false;
			} else {
				report(", ");
			}
			report("%d=%s", gprintVar(var(lits[i])), printWeight(*w).c_str());
		}
		report("\n");
	}

	return true;
}

bool AggSolver::addAggrExpr(Var headv, int setid, Weight bound, AggSign boundsign, AggType type, AggSem headeq) {
	assert(type==MIN || type==MAX || type==CARD || type==SUM || type==PROD);

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

	// Check whether the head occurs in the body of the set, which is no longer allowed
	// TODO zet in file huidige invoerformaat, zodat de grounder dat kan garanderen
	// TODO moet eigenlijk maar 1 keer gecontroleerd worden, dus later zetten
	for (vsize i = 0; i < set->getWL().size(); i++) {
		if (var(set->getWL()[i]) == headv) { //Exception if head occurs in set itself
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

	// As an approximation because each literal would occur n times (TODO better approximation?), we bump n times
	//ORIG:
	getPCSolver()->varBumpActivity(headv);
	// As another test, we bumped each WL literal log n times, but the varbump activity proved to be extremely expensive, so this has been skipped!
	//for(int i=0; i<log(set->getWL().size())+1; i++){
	//	getPCSolver()->varBumpActivity(headv);
	//}

	//TODO test whether bumping the higher weights more would help?

	aggheads.insert(headv);

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Agg* agg = new Agg(bound, boundsign, head, headeq, type);
	set->addAgg(agg);

	if (verbosity() >= 5) { //Print info on added aggregate
		print(agg);
		report("\n");
	}

	return true;
}

void AggSolver::finishParsing(bool& present, bool& unsat) {
	unsat = false;
	present = true;

	if (parsedSets().size() == 0) {
		present = false;
		notifyInitialized();
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

	//Rewrite all sum and card constraint into CNF using PBSOLVER
	if(getPCSolver()->modes().pbsolver && !unsat){
		unsat = !transformSumsToCNF(sets(), getPCSolver());
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, all converted into CNF.\n");
		}
		//FIXME: problems when there are also recursive aggregates!
		notifyInitialized();
		return;
	}

	//Finish the sets: add all body literals to the network
	vps remainingsets;
	vps satsets;
	for (vsize i=0; !unsat && i<sets().size(); i++) {
		TypedSet* set = sets()[i];

		if(set->getAgg().size()==0){
			satsets.push_back(set);
			continue;
		}

		/*for(int i=0; i<set->getAgg().size(); i++){
			assert(set->getAgg()[i]!=NULL);
		}*/
		unsat = unsat || !transformTypePartition(set, sets());
		unsat = unsat || !transformMinToMax(set, sets());
		unsat = unsat || !transformAddTypes(set, sets());
		unsat = unsat || !transformVerifyWeights(set, sets());
		unsat = unsat || !transformSetReduction(set, sets());
		unsat = unsat || !transformCardGeqOneToEquiv(set, sets());
		if(getPCSolver()->modes().pw){ //use PWatches
			unsat = unsat || !transformOneToOneSetToAggMapping(set, sets());
		}

		bool sat = false;
		if(!unsat){
			set->initialize(unsat, sat);
		}

		if(!unsat && !sat){
			for (vsize i = 0; i < set->getWL().size(); i++) {
				network[var(set->getWL()[i])].push_back(set);
			}
		}

		if(sat){
			satsets.push_back(set);
		}else{
			remainingsets.push_back(set);
		}
	}
	sets().clear();
	sets().insert(sets().begin(), remainingsets.begin(), remainingsets.end());
	deleteList<TypedSet>(satsets);

#ifdef DEBUG
	for(int j=0; j<sets().size(); j++){
		for (vpagg::const_iterator i = sets()[j]->getAgg().begin(); i<sets()[j]->getAgg().end(); i++) {
			assert(sets()[j]==(*i)->getSet());
			assert((*i)->getSet()->getAgg()[(*i)->getIndex()]==(*i));
		}
	}
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
	for (vsize i = 0; i < sets().size(); i++) {
		int agg = sets()[i]->getAgg().size();
		totalagg += agg;
		setlits += sets()[i]->getWL().size();
		nbaggs[sets()[i]->getType().getType()]+=agg; //Defaults to 0 if new: http://forums.whirlpool.net.au/archive/1286863
	}

	if (totalagg == 0) {
		if (verbosity() >= 3) {
			report("Initializing aggregates finished, no aggregates present after initialization.\n");
		}
		present = false;
		notifyInitialized();
		return;
	}

	//Print lots of information
	if (verbosity() >= 1) {
		report("| Number of minimum exprs.:     %4zu                                          |\n", nbaggs[MIN]);
		report("| Number of maximum exprs.:     %4zu                                          |\n", nbaggs[MAX]);
		report("| Number of sum exprs.:         %4zu                                          |\n", nbaggs[SUM]);
		report("| Number of product exprs.:     %4zu                                          |\n", nbaggs[PROD]);
		report("| Number of cardinality exprs.: %4zu                                          |\n", nbaggs[CARD]);

		report("| Over %4d sets, aggregate set avg. size: %7.2f lits.                      |\n",
				sets().size(),(double)setlits/(double)(sets().size()));
	}

	if (verbosity() >= 3) {
		report("Aggregates are present after initialization:\n");
		for (vps::const_iterator i = sets().begin(); i < sets().end(); i++) {
			for (vpagg::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); j++) {
				Aggrs::printAgg(**j, true);
			}
		}

		for (vsize i = 0; i < nVars(); i++) {
			report("Watches of var %d:\n", gprintVar(i));
			if (headwatches[i] != NULL) {
				report("   headwatch\n");
				report("      ");
				Aggrs::printAgg(*headwatches[i]->getSet(), true);
			}

			if (verbosity() >= 6) {
				report("   bodywatches\n");
				for (vsize j = 0; j < permwatches[i].size(); j++) {
					report("      ");
					Aggrs::printAgg(*(permwatches[i][j])->getSet(), true);
				}
				for (vsize j = 0; j < tempwatches[i].size(); j++) {
					report("      ");
					Aggrs::printAgg(*(tempwatches[i][j])->getSet(), true);
				}
			}
		}
	}

	//Push initial level (root, before any decisions).
	trail.push_back(vector<TypedSet*>());
	for(int i=0; i<sets().size(); i++){
		trail.back().push_back(sets()[i]);
	}

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
	const Lit& p = ar->getPropLit();

	//FIXME decide on what to do with it
	//This strongly improves the performance of some benchmarks, e.g. FastFood. For Hanoi it has no effect
	//for Sokoban it DECREASES performance!
	//TODO new IDEA: mss nog meer afhankelijk van het AANTAL sets waar het in voorkomt of de grootte van de sets?
	//want de grootte van de set bepaalt hoe vaak de literal zou zijn uitgeschreven in een cnf theorie
	//maar niet trager voor pakman
	getPCSolver()->varBumpActivity(var(p));

	if (value(p) != l_True && getPCSolver()->modes().aggclausesaving < 2) {
		vec<Lit> lits;
		lits.push(p);
		ar->getAgg().getSet()->getExplanation(lits, *ar);
		ar->setClause(lits);
		//FIXME why not return here or something and what with conflicts?
	}

	if (value(p) == l_False) {
		if (verbosity() >= 2) {
			report("Deriving conflict in ");
			gprintLit(p, l_True);
			report(" because of the aggregate expression ");
			Aggrs::printAgg(ar->getAgg(), true);
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
		if (verbosity() >= 2) {
			report("Deriving ");
			gprintLit(p, l_True);
			report(" because of the aggregate expression ");
			Aggrs::printAgg(ar->getAgg(), true);
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
	//report("New decision level\n");
	if (verbosity() >= 6) {
		report("Current effective watches on new decision level: \n");
		//FIXME when partial watches code has been changed printWatches(this, tempwatches);
	}
	trail.push_back(vector<TypedSet*>());
}

void AggSolver::backtrackDecisionLevels(int nblevels, int untillevel) {
	while(trail.size()>untillevel+1){
		//report("Backtrack decision level\n");
		for(vector<TypedSet*>::iterator j=trail.back().begin(); j<trail.back().end(); j++){
			(*j)->backtrack(nblevels, untillevel);
		}
		trail.pop_back();
	}
}

/**
 * Returns non-owning pointer
 */
rClause AggSolver::propagate(const Lit& p) {
	if (!isInitialized()) {
		return nullPtrClause;
	}

	rClause confl = nullPtrClause;

	if (verbosity() >= 2) {
		report("Aggr_propagate("); gprintLit(p, l_True); report(").\n");
	}

	Agg* pa = headwatches[var(p)];
	if (pa != NULL) {
		confl = pa->getSet()->propagate(*pa, getLevel());
		propagations++;
	}

	const vector<Watch*>& ws = permwatches[var(p)];
	for (vector<Watch*>::const_iterator i = ws.begin(); confl == nullPtrClause && i < ws.end(); i++) {
		confl = (*i)->getSet()->propagate(p, *i, getLevel());
		propagations++;
	}

	if (confl != nullPtrClause) {
		return confl;
	}

	if (tempwatches[toInt(p)].size() > 0) {
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

		if (verbosity() >= 8) {
			report("Current effective watches AFTER: \n");
			//FIXME when partial watches code has been changed printWatches(this, tempwatches);
		}
	}

	return confl;
}

rClause	AggSolver::propagateAtEndOfQueue(){
	if (!isInitialized()) {
		return nullPtrClause;
	}

	rClause confl = nullPtrClause;
	for(vector<TypedSet*>::const_iterator i=trail.back().begin(); confl==nullPtrClause && i<trail.back().end(); i++){
		confl = (*i)->propagateAtEndOfQueue(getLevel());
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

	//getPCSolver()->varBumpActivity(var(p));

	rClause c = nullPtrClause;
	if (getPCSolver()->modes().aggclausesaving < 2) {
		assert(getPCSolver()->modes().aggclausesaving>0);
		assert(ar.hasClause());

		//for(int i=0; i<ar.getClause().size(); i++){
		// getPCSolver()->varBumpActivity(var(ar.getClause()[i]));
		// }

		c = getPCSolver()->createClause(ar.getClause(), true);
	} else {
		vec<Lit> lits;
		lits.push(p);
		ar.getAgg().getSet()->getExplanation(lits, ar);

		//for(int i=0; i<lits.size(); i++){
		// getPCSolver()->varBumpActivity(var(lits[i]));
		// }

		//create a conflict clause and return it
		c = getPCSolver()->createClause(lits, true);
	}

	//getPCSolver()->addLearnedClause(c);
	//Adding directly as a learned clause should NOT be done,
	//only when used as direct conflict reason: real slowdown for magicseries

	return c;
}

///////
// RECURSIVE AGGREGATES
///////

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		- have not been added already(seen[A]==1 for A, seen[A]==2 for ~A)
 * 		- might help to make the expression true (monotone literals!) (to make it a more relevant learned clause
 */
void AggSolver::addExternalLiterals(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) {
	const Agg& agg = *getAggWithHead(v);
	TypedSet* set = agg.getSet();

	for (vwl::const_iterator i = set->getWL().begin(); i < set->getWL().end(); ++i) {
		Lit l = (*i).getLit();
		if (set->getType().isMonotone(agg, *i) && ufs.find(var(l)) == ufs.end() && seen[var(l)] != (isPositive(l) ? 2 : 1) && isFalse(l)) {
			//TODO deze laatste voorwaarde is een HACK: eigenlijk moeten de voorwaarden zo zijn,
			//dat enkel relevant literals worden toegevoegd, maar momenteel worden er ook literals
			//toegevoegd die nooit in een justification zullen zitten
			assert(isFalse(l));
			loopf.push(l);
			seen[var(l)] = isPositive(l) ? 2 : 1;
		}
		//TODO: optimize this: neem er zoveel monotone niet zodat ze met de ufs erbij het agg nog true kunnen maken, maar zonder niet
	}
}

vector<Var> AggSolver::getAggHeadsWithBodyLit(Var x) {
	vector<Var> heads;
	for (vps::const_iterator i = network[x].begin(); i < network[x].end(); i++) {
		for (vpagg::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); j++) {
			heads.push_back(var((*j)->getHead()));
		}
	}
	return heads;
}

vwl::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggWithHead(x)->getSet()->getWL().begin();
}

vwl::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggWithHead(x)->getSet()->getWL().end();
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in heads, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, vec<Var>& currentjust) {
	for (vps::const_iterator i = network[var(w)].begin(); i < network[var(w)].end(); i++) {
		TypedSet* s = (*i);
		for (vpagg::const_iterator j = s->getAgg().begin(); j < s->getAgg().end(); j++) {
			const Agg& expr = *(*j);
			if (isFalse(expr.getHead())) {
				continue;
			}

			Var head = var(expr.getHead());
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf;
				vec<Var> nonjstf;
				if (s->getType().canJustifyHead(expr, jstf, nonjstf, currentjust, false)) {
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
	vec<int> currentjust;
	const Agg& agg = *getAggWithHead(head);
	agg.getSet()->getType().canJustifyHead(agg, outjstf, nonjstf, currentjust, true);
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	const Agg& agg = *getAggWithHead(v);
	return agg.getSet()->getType().canJustifyHead(agg, jstf, nonjstf, currentjust, false);
}

///////
// OPTIMIZATION
///////

//FIXME no optimizations should take place on mnmz aggregates (partially helped by separate add method).
bool AggSolver::addMnmzSum(Var headv, int setid, AggSign boundsign) {
	if (parsedSets().find(setid) == parsedSets().end()) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(headv>=0);

	TypedSet* set = parsedSets()[setid];

	// Check whether the head occurs in the body of the set, which is no longer allowed
	for (vsize i = 0; i < set->getWL().size(); i++) {
		if (var(set->getWL()[i]) == headv) { //Exception if head occurs in set itself
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

	Weight max = 0, min = 0;
	for (vwl::const_iterator i = set->getWL().begin(); i < set->getWL().end(); i++) {
		if ((*i).getWeight() > 0) {
			max += (*i).getWeight();
		} else {
			min += (*i).getWeight();
		}
	}

	Agg* ae = new Agg(boundsign == LB ? max + 1 : min, boundsign, head, COMP, SUM);
	set->addAgg(ae);
	ae->setOptim();

	if (verbosity() >= 3) {
		report("Added sum minimization: Minimize ");
		print(ae);
		report("\n");
	}

	return true;
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head) {
	Agg* a = headwatches[head];
	TypedSet* s = a->getSet();
	SumFWAgg* prop = dynamic_cast<SumFWAgg*> (s->getProp());

	report("Current optimum: %s\n", printWeight(prop->getCC()).c_str());

	a->setBound(prop->getCC() - 1);

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
	dynamic_cast<SumFWAgg*>(headwatches[head]->getSet()->getProp())->propagate(*headwatches[head], true);
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

void AggSolver::print(Agg* agg) const{
	report("Added %s aggregate with head %d on set %d, %s %s of type ",
			agg->getSem() == DEF?"defined":"completion",
			gprintVar(var(agg->getHead())),
			agg->getSetID(),
			agg->getSign()==LB?"AGG <=":"AGG >=",
			printWeight(agg->getBound()).c_str());
	switch (agg->getType()) {
	case SUM:
		report("SUM");
		break;
	case CARD:
		report("CARD");
		break;
	case MIN:
		report("MIN");
		break;
	case MAX:
		report("MAX");
		break;
	case PROD:
		report("PROD");
		break;
	}
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
