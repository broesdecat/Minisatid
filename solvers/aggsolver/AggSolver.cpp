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

#include "solvers/aggsolver/AggSolver.hpp"

#include "solvers/utils/Utils.hpp"
#include "solvers/utils/Print.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

#include "solvers/aggsolver/AggComb.hpp"

#include "solvers/aggsolver/FullyWatched.hpp"

#include <algorithm>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

AggSolver::AggSolver(pPCSolver s) :
	SolverModule(s), propagations(0) {
	int count = 0;
	maptype.operator [](MAX) = count++;
	maptype.operator [](CARD) = count++;
	maptype.operator [](PROD) = count++;
	maptype.operator [](SUM) = count++;
	maptype.operator [](MIN) = count++;
	sets.resize(count);
}

AggSolver::~AggSolver() {
	for(vector<vector<paggs> >::const_iterator i=sets.begin(); i<sets.end(); i++){
		deleteList<aggs> (*i);
	}
	deleteList<AggReason> (aggreason);
}

void AggSolver::notifyVarAdded(uint64_t nvars) {
	assert(headwatches.size() < nvars);
	headwatches.resize(nvars, NULL);
	permwatches.resize(nvars);
	tempwatches.resize(2 * nvars);
	aggreason.resize(nvars, NULL);
	network.resize(nvars);
}

void AggSolver::setHeadWatch(Var head, Agg* agg) {
	headwatches[head] = agg;
	if (agg->isDefined()) {
		getPCSolver()->notifyAggrHead(head);
	}
}

void AggSolver::removeHeadWatch(Var x) {
	//delete headwatches[x];
	headwatches[x] = NULL;
	getPCSolver()->removeAggrHead(x);
}

void AggSolver::addPermWatch(Var v, pw w) {
	permwatches[v].push_back(w);
}

void AggSolver::addTempWatch(const Lit& l, pw w) {
	tempwatches[toInt(l)].push_back(w);
}

inline pagg AggSolver::getAggWithHead(Var v) const {
	assert(headwatches[v] != NULL);
	return headwatches[v];
}

void AggSolver::finishParsing(bool& present, bool& unsat) {
	notifyInitialized();

	unsat = false;
	present = true;

	if (sets[maptype[MAX]].size() == 0) {
		present = false;
		return;
	}

	if (verbosity() >= 3) {
		reportf("Initializing all sets:\n");
	}

	for(vector<vector<paggs> >::iterator i=sets.begin(); i<sets.end(); i++){
		if (!finishSets(*i)){
			unsat = true;
			if (verbosity() >= 3) {
				reportf("Initializing aggregates finished, unsat detected.\n");
			}
			return;
		}
	}

	if (verbosity() >= 1) {
		int agg = 0;
		for (int i = 0; i < sets[maptype[MAX]].size(); i++) {
			agg += sets[maptype[MAX]][i]->getAgg().size();
		}
		reportf("| Number of maximum exprs.: %4zu                                              |\n", agg);

		agg = 0;
		for (int i = 0; i < sets[maptype[SUM]].size(); i++) {
			agg += sets[maptype[SUM]][i]->getAgg().size();
		}
		reportf("| Number of sum exprs.: %4zu                                                  |\n", agg);

		agg = 0;
		for (int i = 0; i < sets[maptype[PROD]].size(); i++) {
			agg += sets[maptype[PROD]][i]->getAgg().size();
		}
		reportf("| Number of product exprs.: %4zu                                              |\n", agg);

		agg = 0;
		for (int i = 0; i < sets[maptype[CARD]].size(); i++) {
			agg += sets[maptype[CARD]][i]->getAgg().size();
		}
		reportf("| Number of cardinality exprs.: %4zu                                          |\n",
					agg);

		int nb_sets=0, total_nb_set_lits = 0;
		for(vector<vector<paggs> >::const_iterator i=sets.begin(); i<sets.end(); i++){
			for(vector<paggs>::const_iterator j=(*i).begin(); j<(*i).end(); j++){
				nb_sets++;
				total_nb_set_lits += (*j)->getWL().size();
			}
		}
		reportf("| Over %4d sets, aggregate set avg. size: %7.2f lits.                      |\n",
				nb_sets,(double)total_nb_set_lits/(double)(nb_sets));
	}

	if (verbosity() >= 3) {
		if (verbosity() >= 3) {
			reportf("Aggregates present after initialization: \n");
			for (vector<vector<paggs> >::iterator i = sets.begin(); i<sets.end(); i++) {
				for (vector<paggs>::iterator j = (*i).begin(); j<(*i).end(); j++) {
					Aggrs::printAgg(*j);
				}
			}
		}

		int counter = 0;
		for (vector<vector<pw> >::const_iterator i = permwatches.begin(); i < permwatches.end(); i++, counter++) {
			reportf("Watches of var %d:\n", gprintVar(counter));
			if (headwatches[counter] != NULL) {
				reportf("HEADwatch = ");
				Aggrs::printAgg(headwatches[counter]->getAggComb(), true);
			}
			for (vector<pw>::const_iterator j = (*i).begin(); j< (*i).end(); j++) {
				Aggrs::printAgg((*j)->getAggComb(), true);
			}
		}

		reportf("Initializing finished.\n");
	}

	bool allempty = true;
	for(vector<vector<paggs> >::const_iterator i=sets.begin(); allempty && i<sets.end(); i++){
		if ((*i).size()!=0){
			allempty = false;
		}
	}
	if(allempty){
		present = false;
	}
}

bool AggSolver::finishSets(vector<paggs>& sets) {
	vector<paggs>::size_type used = 0;
	for (vector<paggs>::size_type i = 0; i < sets.size(); i++) {
		paggs s = sets[i];

		bool unsat;
		paggs s2 = s->initialize(unsat);
		if (unsat) {
			return false; //Problem is UNSAT
		}
		if (s2 != s) {
			delete s;
			s = s2;
		}
		if (s != NULL) {
			sets[used++] = s;
			for (vwl::size_type j = 0; j < s->getWL().size(); j++) {
				Var v = var(s->getWL()[j].getLit());
				network[v].push_back(s);
			}
		}
	}
	sets.resize(used);

	return true;
}

/*void AggSolver::findClausalPropagations(){
 int counter = 0;
 for(int i=0; i<aggrminsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrminsets[i]->getWLBegin(); j<aggrminsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(int i=0; i<aggrprodsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrprodsets[i]->getWLBegin(); j<aggrprodsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(int i=0; i<aggrsumsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrsumsets[i]->getWLBegin(); j<aggrsumsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 for(int i=0; i<aggrmaxsets.size(); i++){
 vector<Var> set;
 for(lwlv::const_iterator j=aggrmaxsets[i]->getWLBegin(); j<aggrmaxsets[i]->getWLEnd(); j++){
 set.push_back(var((*j).getLit()));
 }
 counter += getPCSolver()->getClausesWhichOnlyContain(set).size();
 }
 reportf("Relevant clauses: %d.\n", counter);
 }*/

bool AggSolver::addSet(int setid, const vector<Lit>& lits,
		const vector<Weight>& weights) {
	assert(setid > 0);
	uint64_t setindex = setid - 1;
	if (lits.size() == 0) {
		char s[100];
		sprintf(s, "Set nr. %d is empty.\n", setid);
		throw idpexception(s);
	}
	if (sets[0].size() > setindex && sets[0][setindex] != NULL
			&& sets[0][setindex]->getWL().size() != 0) {
		char s[100];
		sprintf(s, "Set nr. %d is defined more than once.\n", setid);
		throw idpexception(s);
	}

	vector<WL> lw, invlw; //inverted weights to handle minimum as maximum
	for (int i = 0; i < lits.size(); i++) {
#ifdef INTWEIGHT
		if (weights[i] == INT_MAX || weights[i] == INT_MIN) {
			throw idpexception(
					"Weights equal to or larger than the largest integer number "
						"are not allowed in limited precision.\n");
		}
#endif
		lw.push_back(WL(lits[i], weights[i]));
		invlw.push_back(WL(lits[i], -weights[i]));
	}

	if (verbosity() >= 5) {
		reportf("Added set %d: ", setid);
		vector<Weight>::const_iterator w = weights.begin();
		bool begin = true;
		for (int i = 0; i < lits.size(); i++, w++) {
			if (begin) {
				begin = false;
			} else {
				reportf(", ");
			}
			reportf("%d=%s", gprintVar(var(lits[i])), printWeight(*w).c_str());
		}
		reportf("\n");
	}

	while (sets[0].size() <= setindex) {
		sets[maptype[MAX]].push_back(new MaxCalc(this, lw));
		sets[maptype[SUM]].push_back(new SumCalc(this, lw));
		sets[maptype[PROD]].push_back(new ProdCalc(this, lw));
		//sets[maptype[CARD]].push_back(new CardPWAgg(this, lw));
		sets[maptype[CARD]].push_back(new SumCalc(this, lw));
		sets[maptype[MIN]].push_back(new MaxCalc(this, invlw));
	}

	return true;
}

bool AggSolver::addAggrExpr(Var headv, int setid, Weight bound,
		Bound boundsign, AggrType type, HdEq headeq) {
	if (((vector<int>::size_type) setid) > sets[0].size() || sets[0][setid - 1]
			== NULL || sets[0][setid - 1]->getWL().size() == 0) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(headv > -1);
	uint64_t nb = headv;

	//INVARIANT: it has to be guaranteed that there is a watch on ALL heads
	if (headwatches.size() > nb && headwatches[headv] != NULL) {
		char s[100];
		sprintf(s, "Two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}

	assert(headwatches.size() > nb);

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	// These guys ought to be initially a bit more important then the rest.
	getPCSolver()->varBumpActivity(var(head));

	assert(setid > 0);
	int setindex = setid - 1;

	pagg ae;
	paggs c;
	switch (type) {
	case MIN:
		//return maxAggAsSAT(defined, !lower, -bound, head, *aggrminsets[setindex]);
		boundsign = (boundsign == LOWERBOUND ? UPPERBOUND : LOWERBOUND);
		c = sets[maptype[MIN]][setindex];
		ae = new Agg(-bound, boundsign, head, headeq);
		c->addAgg(ae);
		break;
	case MAX:
		//return maxAggAsSAT(defined, lower, bound, head, *aggrmaxsets[setindex]);
		c = sets[maptype[MAX]][setindex];
		ae = new Agg(bound, boundsign, head, headeq);
		c->addAgg(ae);
		break;
	case CARD:
#ifdef DEBUG
		for(vwl::size_type i=0; i<sets[maptype[SUM]][setindex]->getWL().size(); i++) {
			if(sets[maptype[SUM]][setindex]->getWL()[i].getWeight()!=1) {
				reportf("Cardinality was loaded with wrong weights");
			}
		}
#endif
		// Flow over into sum!
	case SUM: {
		// If all weights are 1, add as a cardinality, otherwise add as a sum.
		bool allone = true;
		for (vwl::const_iterator i =
				sets[maptype[SUM]][setindex]->getWL().begin(); allone && i
				< sets[maptype[SUM]][setindex]->getWL().end(); i++) {
			if ((*i).getWeight() != 1) {
				allone = false;
			}
		}
		if (allone) {
			c = sets[maptype[CARD]][setindex];
		} else {
			c = sets[maptype[SUM]][setindex];
		}
		ae = new Agg(bound, boundsign, head, headeq);
		c->addAgg(ae);
		break;
	}
	case PROD:
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for (vwl::const_iterator i =
				sets[maptype[PROD]][setindex]->getWL().begin(); i
				< sets[maptype[PROD]][setindex]->getWL().end(); i++) {
			if ((*i).getWeight() < 1) {
				char s[200];
				sprintf(
						s,
						"Error: Set nr. %d contains a 0 (zero) or negative weight %s, which cannot "
							"be used in combination with a product aggregate\n",
						setid, printWeight((*i).getWeight()).c_str());
				throw idpexception(s);
			}
		}
		c = sets[maptype[PROD]][setindex];
		ae = new Agg(bound, boundsign, head, headeq);
		c->addAgg(ae);
		break;
	default:
		assert(false);
		throw idpexception(
				"Only aggregates MIN, MAX, CARD, SUM or PROD are allowed in the solver.\n");
	}

	if (verbosity() >= 5) {
		reportf("Added %s aggregate with head %d on set %d, %s %s of type %s.\n",
				headeq == DEF?"defined":"completion", gprintVar(headv), setid,
				boundsign==LOWERBOUND?"AGG <=":"AGG >=", printWeight(bound).c_str(),
				c->getName());
	}

	return true;
}

/**
 * The method propagates the fact that p has been derived to the SAT solver. If a conflict occurs,
 * a conflict clause is returned. Otherwise, the value is set to true in the sat solver.
 *
 * @pre: literal p can be derived to be true because of the given aggregate reason
 *
 * @remarks: only method allowed to use the sat solver datastructures
 *
 * Returns non-owning pointer
 */
rClause AggSolver::notifySolver(const Lit& p, AggReason* ar) {
	//FIXME decide on what to do with it
	//This strongly improves the performance of some benchmarks, e.g. FastFood. For Hanoi it has no effect
	//for Sokoban is DECREASES performance!
	//TODO new IDEA: mss nog meer afhankelijk van het AANTAL sets waar het in voorkomt?
	//WILL ALSO IMPROVE WITH WATCHES
	getPCSolver()->varBumpActivity(var(p));

	if (value(p) == l_False) {
		if (verbosity() >= 2) {
			reportf("Deriving conflict in ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			Aggrs::printAgg(ar->getAgg());
		}
		AggReason* old_ar = aggreason[var(p)];
		aggreason[var(p)] = ar;
		rClause confl = getExplanation(p);
		getPCSolver()->addLearnedClause(confl);

		aggreason[var(p)] = old_ar;
		delete ar;

		return confl;
	} else if (value(p) == l_Undef) {
		if (verbosity() >= 2) {
			reportf("Deriving ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			Aggrs::printAgg(ar->getAgg());
		}
		assert(aggreason[var(p)] == NULL);
		aggreason[var(p)] = ar;
		getPCSolver()->setTrue(p);
	} else {
		delete ar;
	}
	return nullPtrClause;
}

void AggSolver::newDecisionLevel() {
	int found = 0;
	//Only for one watched set! FIXME: remove after testing
	for (int i = 0; i < tempwatches.size(); i++) {
		if (tempwatches[i].size() == 0) {
			continue;
		}
		reportf("Temp watches ");
		gprintLit(toLit(i));
		reportf(": ");
		if (value(toLit(i)) == l_True) {
			found++;
			reportf("TRUE");
		}else if(value(toLit(i)) == l_False){
			reportf("FALSE");
		}
		reportf("\n");
	}
	assert(found <= 1);
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
		reportf("Aggr_propagate(");
		gprintLit(p, l_True);
		reportf(").\n");
	}

	pagg pa = headwatches[var(p)];
	if (pa != NULL) {
		confl = pa->getAggComb()->propagate(*pa);
		propagations++;
	}

	vector<pw>& ws = permwatches[var(p)];
	for (vector<pw>::const_iterator i = ws.begin(); confl == nullPtrClause && i
			< ws.end(); i++) {
		confl = (*i)->getAggComb()->propagate(p, **i);
		propagations++;
	}

	if (confl != nullPtrClause) {
		return confl;
	}

	vector<pw> ws2 = tempwatches[toInt(p)]; //IMPORTANT, BECAUSE WATCHES MIGHT BE ADDED AGAIN TO THE END (if no other watches are found etc)
	tempwatches[toInt(p)].clear();

	if (verbosity() >= 3) {
		reportf("Watched set for ");
		gprintLit(p);
		reportf(": ");
		for (int i = 0; i < ws2.size(); i++) {
			gprintLit(ws2[i]->getWL().getLit());
			reportf(", ");
		}
		reportf("\n");
	}

	int i = 0;
	bool deleted = false;
	for (; confl == nullPtrClause && i < ws2.size(); i++) {
		confl = ws2[i]->getAggComb()->propagate(p, *ws2[i]);
		propagations++;
		if (confl == nullPtrClause) {
			delete ws2[i];
			deleted = true;
		}
	}
	if (deleted) {
		for (; i < ws2.size(); i++){
			tempwatches[toInt(p)].push_back(tempwatches[toInt(p)][i]);
		}
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

	//get the explanation from the aggregate expression
	vec<Lit> lits;
	lits.push(p);

	ar.getAgg().getAggComb()->getExplanation(lits, ar);

	//create a conflict clause and return it
	rClause c = getPCSolver()->createClause(lits, true);
	//getPCSolver()->addLearnedClause(c);
	//Adding directly as a learned clause should NOT be done: real slowdown for magicseries

	if (verbosity() >= 2) {
		reportf("Implicit aggregate reason clause for ");
		gprintLit(p, sign(p) ? l_False : l_True);
		reportf(" : ");
		Print::printClause(c, getPCSolver());
		reportf("\n");
	}

	return c;
}

/**
 * Not viable to backtrack a certain number of literals, unless also tracking whether a literal was propagated in
 * which solvers when a conflict occurred
 */
void AggSolver::backtrack(const Lit& l) {
	if (!isInitialized()) {
		return;
	}

	if (aggreason[var(l)] != NULL) {
		delete aggreason[var(l)];
		aggreason[var(l)] = NULL;
	}

	pagg pa = headwatches[var(l)];
	if (pa != NULL) {
		pa->getAggComb()->backtrack(*pa);
	}

	vector<pw>& vcw = permwatches[var(l)];
	for (vector<pw>::const_iterator i = vcw.begin(); i < vcw.end(); i++) {
		(*i)->getAggComb()->backtrack(**i);
	}
}

///////
// RECURSIVE AGGREGATES
///////

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		have not been added already(seen[A]==1 for A, seen[A]==2 for ~A)
 * 		might help to make the expression true (monotone literals!)
 */
void AggSolver::addExternalLiterals(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) {
	const Agg& agg = *getAggWithHead(v);
	paggs comb = agg.getAggComb();

	for (vwl::const_iterator i = comb->getWL().begin(); i < comb->getWL().end(); ++i) {
		Lit l = (*i).getLit();
		if (comb->isMonotone(agg, *i) && ufs.find(var(l)) == ufs.end()
				&& seen[var(l)] != (isPositive(l) ? 2 : 1) && isFalse(l)) { //TODO deze laatste voorwaarde is een HACK: eigenlijk moeten de voorwaarden zo zijn, dat enkel relevant literals worden toegevoegd, maar momenteel worden er ook literals toegevoegd die nooit in een justification zullen zitten
			assert(isFalse(l));
			loopf.push(l);
			seen[var(l)] = isPositive(l) ? 2 : 1;
		}
		//TODO en neem er zoveel monotone niet zodat ze met de ufs erbij het agg nog true kunnen maken, maar zonder niet
	}
}

vector<Var> AggSolver::getAggHeadsWithBodyLit(Var x){
	vector<Var> heads;
	for(vector<paggs>::const_iterator i=network[x].begin(); i<network[x].end(); i++){
		for(vpagg::const_iterator j=(*i)->getAgg().begin(); j<(*i)->getAgg().end(); j++){
			heads.push_back(var((*j)->getHead()));
		}
	}
	return heads;
}

vwl::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggWithHead(x)->getAggComb()->getWL().begin();
}

vwl::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggWithHead(x)->getAggComb()->getWL().end();
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in heads, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, vec<Var>& currentjust) {
	for (vector<paggs>::const_iterator i = network[var(w)].begin(); i< network[var(w)].end(); i++) {
		paggs s = (*i);
		for (vpagg::const_iterator j = s->getAgg().begin(); j < s->getAgg().end(); j++) {
			const Agg& expr = *(*j);
			if (isFalse(expr.getHead())) {
				//reportf(" => head is false %d\n", gprintVar(var(expr->getHead())));
				continue;
			}

			//WRONG WRONG
			//If not monotone, then the head can never become true by w
			//if(!expr->isMonotone((*(set->getWLBegin()+(*i).getIndex())))){
			//	reportf(" => occurence is not monotone in agg %d \n", gprintVar(var(expr->getHead())));
			//	continue;
			//}

			//reportf("=> checking agg %d \n", gprintVar(var(expr->getHead())));

			Var head = var(expr.getHead());
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf;
				vec<Var> nonjstf;
				if (s->canJustifyHead(expr, jstf, nonjstf, currentjust, false)) {
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
	agg.getAggComb()->canJustifyHead(agg, outjstf, nonjstf, currentjust, true);
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf,
		vec<Var>& currentjust) {
	const Agg& agg = *getAggWithHead(v);
	return agg.getAggComb()->canJustifyHead(agg, jstf, nonjstf, currentjust,
			false);
}

///////
// OPTIMIZATION
///////

//FIXME no optimizations should take place on mnmz aggregates (partially helped by separate add method).
//FIXME 2 more optimization should/could take place on other aggregates
bool AggSolver::addMnmzSum(Var headv, int setid, Bound boundsign) {
	/* FIXME
	if (((vector<int>::size_type) setid)>sets[0].size() || sets[0][setid-1]==NULL || sets[0][setid-1]->getWL().size()==0) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(setid>0);
	assert(headv>0);
	uint64_t nb = headv;

	if (headwatches.size() > nb && headwatches[headv] != NULL) {
		char s[100];
		sprintf(s, "Two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}

	assert(headwatches.size()>nb);

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Weight max = 0, min = 0;
	for(lwlv::const_iterator i=sets[maptype[SUM]][setid-1]->getWL().begin(); i<sets[maptype[SUM]][setid-1]->getWL().end(); i++){
		if((*i).getWeight()>0){
			max += (*i).getWeight();
		}else{
			min += (*i).getWeight();
		}
	}

	pagg ae = new SumAgg(boundsign, boundsign==LOWERBOUND ? max+1 : min, head, pset(sets[maptype[SUM]][setid-1]));
	ae->setOptimAgg(); //FIXME temporary solution
	aggregates.push_back(ae);
	headwatches[var(head)] = ae;


	if (verbosity() >= 3) {
		reportf("Added sum minimization: Minimize ");
		printAggrExpr(ae);
		reportf("\n");
	}

	return true;*/
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head) {
	/* TODO
	pagg a = headwatches[head];
	pset s = a->getSet();

	reportf("Current optimum: %s\n", printWeight(s->getCC()).c_str());

	if (a->isLower()) {
		a->setLowerBound(s->getCC() - 1);
	} else if (a->isUpper()) {
		a->setUpperBound(s->getCC() - 1);
	}

	if (s->getBestPossible() == s->getCC()) {
		return true;
	}

	s->getMinimExplan(*a, invalidation);

	return false;*/
}

/**
 * FIXME: not really beautiful solution, maybe it can be fixed with ASSUMPTIONS?
 * This method has to be called after every temporary solution has been found to force the propagation of
 * the newly adapted bound.
 */
void AggSolver::propagateMnmz(Var head) {
	dynamic_cast<SumFWAgg*> (headwatches[head]->getAggComb())->propagate(*headwatches[head], true);
}

///////
// PRINTING
///////

void AggSolver::printStatistics() const {
	reportf("aggregate propagations: %-12" PRIu64 "\n", propagations);
}
