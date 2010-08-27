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

#include "solvers/aggsolver/Agg.hpp"
#include "solvers/aggsolver/AggSets.hpp"

#include "solvers/utils/Utils.hpp"
#include "solvers/utils/Print.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

#include <algorithm>

AggSolver::AggSolver(pPCSolver s) :
	SolverModule(s) {
	int count = 0;
	maptype.operator [](CARD) = count++;
	maptype.operator [](MAX) = count++;
	maptype.operator [](PROD) = count++;
	maptype.operator [](SUM) = count++;
	maptype.operator [](MIN) = count++;
	sets.resize(count);
}

AggSolver::~AggSolver() {
	deleteList<Agg> (aggregates);
	for(vector<vector<pSet> >::const_iterator i=sets.begin(); i<sets.end(); i++){
		deleteList<AggSet> (*i);
	}
	deleteList<AggrReason> (aggr_reason);
}

void AggSolver::removeHeadWatch(Var x) {
	head_watches[x] = NULL;
	getPCSolver()->removeAggrHead(x);
}

void AggSolver::notifyVarAdded(uint64_t nvars) {
	assert(head_watches.size()<nvars);
	head_watches.resize(nvars, NULL);
	aggr_watches.resize(nvars);
	aggr_reason.resize(nvars, NULL);
	network.resize(nvars);
	tempwatches.resize(2*nvars);
}

void AggSolver::addTempWatch(const Lit& l, pSet set){
	tempwatches[toInt(~l)].push_back(set);
}

inline pAgg AggSolver::getAggWithHeadOccurence(Var v) const {
	assert(head_watches[v]!=NULL);
	return head_watches[v];
}

void AggSolver::finishECNF_DataStructures(bool& present, bool& unsat) {
	notifyInitialized();

	unsat = false;
	present = true;

	if (sets[maptype[MAX]].size() == 0) {
		present = false;
		return;
	}

	if (verbosity() >= 1) {
		reportf("| Number of maximum exprs.: %4zu                                              |\n",
					sets[maptype[MAX]].size());
		reportf("| Number of sum exprs.: %4zu                                                  |\n",
					sets[maptype[SUM]].size());
		reportf("| Number of product exprs.: %4zu                                              |\n",
					sets[maptype[PROD]].size());
		reportf("| Number of cardinality exprs.: %4zu                                          |\n",
					sets[maptype[CARD]].size());

		int nb_sets=0, total_nb_set_lits = 0;
		for(vector<vector<pSet> >::const_iterator i=sets.begin(); i<sets.end(); i++){
			for(vector<pSet>::const_iterator j=(*i).begin(); j<(*i).end(); j++){
				nb_sets++;
				total_nb_set_lits += (*j)->getWL().size();
			}
		}
		reportf("| Over %4d sets, aggregate set avg. size: %7.2f lits.                         |\n",
				nb_sets,(double)total_nb_set_lits/(double)(nb_sets));
	}

	if (verbosity() >= 3) {
		reportf("Initializing all sets:\n");
	}

	for(vector<vector<pSet> >::iterator i=sets.begin(); i<sets.end(); i++){
		if (!finishSets(*i)){
			unsat = true;
			return;
		}
	}

	if (verbosity() >= 3) {
		if (verbosity() >= 3) {
			reportf("Aggregates present after initialization: \n");
			for (vector<vector<pSet> >::iterator i = sets.begin(); i<sets.end(); i++) {
				for (vector<pSet>::iterator j = (*i).begin(); j<(*i).end(); j++) {
					pSet s = *j;
					for (lsagg::const_iterator k = s->getAgg().begin(); k < s->getAgg().end(); k++) {
						Aggrs::printAggrExpr(*k);
					}
				}
			}
		}

		int counter = 0;
		for (vector<vector<AggrWatch> >::const_iterator i =
				aggr_watches.begin(); i < aggr_watches.end(); i++, counter++) {
			reportf("Watches of var %d:\n", gprintVar(counter));
			if (head_watches[counter] != NULL) {
				reportf("HEADwatch = ");
				Aggrs::printAggrExpr(head_watches[counter]);
			}
			for (vector<AggrWatch>::const_iterator j = (*i).begin(); j< (*i).end(); j++) {
				Aggrs::printAggrSet((*j).getSet(), true);
			}
		}

		reportf("Initializing finished.\n");
	}

	bool allempty = true;
	for(vector<vector<pSet> >::const_iterator i=sets.begin(); allempty && i<sets.end(); i++){
		if ((*i).size()!=0){
			allempty = false;
		}
	}
	if(allempty){
		present = false;
	}
}

bool AggSolver::finishSets(vector<pSet>& sets) {
	vector<pSet>::size_type used = 0;
	for (vector<pSet>::size_type i = 0; i < sets.size(); i++) {
		pSet s = sets[i];

		bool unsat;
		s = s->initialize(unsat);
		if (!unsat) {
			return false;	//Problem is UNSAT
		}
		if(s!=NULL){
			sets[used++] = s;
			int index = 0;
			for (lwlv::const_iterator j = s->getWL().begin(); j< s->getWL().end(); j++, index++) {
				Var v = var((*j).getLit());
				network[v].push_back(s);
				aggr_watches[v].push_back(AggrWatch(s, index, sign((*j).getLit()) ? NEG : POS));
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

bool AggSolver::addSet(int setid, const vec<Lit>& lits,	const vector<Weight>& weights) {
	assert(setid>0);
	uint64_t setindex = setid - 1;
	if (lits.size() == 0) {
		char s[100]; sprintf(s, "Set nr. %d is empty.\n", setid);
		throw idpexception(s);
	}
	if (sets[0].size()>setindex && sets[0][setindex]!=NULL && sets[0][setindex]->getWL().size()!=0) {
		char s[100]; sprintf(s, "Set nr. %d is defined more than once.\n", setid);
		throw idpexception(s);
	}

	vector<Weight> weights2; //inverted weights to handle minimum as maximum
	for (vector<Weight>::const_iterator i = weights.begin(); i < weights.end(); i++) {
#ifdef INTWEIGHT
		if (*i == INT_MAX || *i == INT_MIN) {
			throw idpexception("Weights equal to or larger than the largest integer number "
							   "are not allowed in limited precision.\n");
		}
#endif
		weights2.push_back(-Weight(*i));
	}

	if (verbosity() >= 5) {
		reportf("Added set %d: ", setid);
		vector<Weight>::const_iterator w = weights.begin();
		bool begin = true;
		for (int i = 0; i < lits.size(); i++, w++) {
			if(begin){
				begin = false;
			}else{
				reportf(", ");
			}
			reportf("%d=%s", gprintVar(var(lits[i])), printWeight(*w).c_str());
		}
		reportf("\n");
	}

	while (sets[0].size() <= setindex) {
		sets[maptype[MAX]].push_back(new AggrMaxSet(lits, weights, this));
		sets[maptype[SUM]].push_back(new AggrSumSet(lits, weights, this));
		sets[maptype[PROD]].push_back(new AggrProdSet(lits, weights, this));
		sets[maptype[MIN]].push_back(new AggrMaxSet(lits, weights2, this));
		sets[maptype[CARD]].push_back(new AggrSumSet(lits, weights, this));
	}

	return true;
}

bool AggSolver::addAggrExpr(Var headv, int setid, Weight bound, Bound boundsign, AggrType type, HdEq headeq) {
	if (((vector<int>::size_type) setid)>sets[0].size() || sets[0][setid-1]==NULL || sets[0][setid-1]->getWL().size()==0) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(headv>-1);
	uint64_t nb = headv;

	//INVARIANT: it has to be guaranteed that there is a watch on ALL heads
	if (head_watches.size() > nb && head_watches[headv] != NULL) {
		char s[100];
		sprintf(s, "Two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}

	assert(head_watches.size()>nb);

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	// These guys ought to be initially a bit more important then the rest.
	getPCSolver()->varBumpActivity(var(head));

	assert(setid>0);
	int setindex = setid - 1;

	pAgg ae;
	switch (type) {
	case MIN:
		//return maxAggAsSAT(defined, !lower, -bound, head, *aggrminsets[setindex]);
		boundsign = (boundsign == LOWERBOUND ? UPPERBOUND : LOWERBOUND);
		ae = pAgg(new MaxAgg(boundsign, -bound, head, pSet(sets[maptype[MIN]][setindex])));
		break;
	case MAX:
		//return maxAggAsSAT(defined, lower, bound, head, *aggrmaxsets[setindex]);
		ae = pAgg(new MaxAgg(boundsign, bound, head, pSet(sets[maptype[MAX]][setindex])));
		break;
	case CARD:
#ifdef DEBUG
		for(lwlv::size_type i=0; i<sets[maptype[SUM]][setindex]->getWL().size(); i++) {
			if(sets[maptype[SUM]][setindex]->getWL()[i].getWeight()!=1) {
				reportf("Cardinality was loaded with wrong weights");
			}
		}
#endif
		// Flow over into sum!
	case SUM: {
		// If all weights are 1, add as a cardinality, otherwise add as a sum.
		bool allone = true;
		for(lwlv::const_iterator i=sets[maptype[SUM]][setindex]->getWL().begin(); allone && i<sets[maptype[SUM]][setindex]->getWL().end(); i++){
			if((*i).getWeight()!=1){
				allone = false;
			}
		}
		if(allone){
			ae = pAgg(new CardAgg(boundsign, bound, head, pSet(sets[maptype[CARD]][setindex])));
		}else{
			ae = pAgg(new SumAgg(boundsign, bound, head, pSet(sets[maptype[SUM]][setindex])));
		}
		break;
	}
	case PROD:
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for (lwlv::const_iterator i = sets[maptype[PROD]][setindex]->getWL().begin(); i< sets[maptype[PROD]][setindex]->getWL().end(); i++) {
			if ((*i).getWeight() < 1) {
				char s[200];
				sprintf(s,
						"Error: Set nr. %d contains a 0 (zero) or negative weight %s, which cannot "
							"be used in combination with a product aggregate\n",
						setid, printWeight((*i).getWeight()).c_str());
				throw idpexception(s);
			}
		}
		ae = pAgg(new ProdAgg(boundsign, bound, head, pSet(sets[maptype[PROD]][setindex])));
		break;
	default:
		assert(false);
		throw idpexception("Only aggregates MIN, MAX, CARD, SUM or PROD are allowed in the solver.\n");
	}

	head_watches[var(head)] = pAgg(ae);

	if (headeq == DEF) { //add as definition to use definition semantics
		//notify the id solver that a new aggregate definition has been added
		getPCSolver()->notifyAggrHead(var(head));
	}

	aggregates.push_back(ae);

	if (verbosity() >= 5) {
		reportf("Added %s aggregate with head %d on set %d, %s %s of type %s.\n", headeq == DEF?"defined":"completion", gprintVar(headv), setid, boundsign==LOWERBOUND?"AGG <=":"AGG >=", printWeight(bound).c_str(), ae->getSet()->getName().c_str());
	}

	return true;
}

//FIXME no optimizations should take place on mnmz aggregates (partially helped by separate add method).
//FIXME 2 more optimization should/could take place on other aggregates
bool AggSolver::addMnmzSum(Var headv, int setid, Bound boundsign) {
	if (((vector<int>::size_type) setid)>sets[0].size() || sets[0][setid-1]==NULL || sets[0][setid-1]->getWL().size()==0) {
		char s[100];
		sprintf(s, "Set nr. %d is used, but not defined yet.\n", setid);
		throw idpexception(s);
	}

	assert(setid>0);
	assert(headv>0);
	uint64_t nb = headv;

	if (head_watches.size() > nb && head_watches[headv] != NULL) {
		char s[100];
		sprintf(s, "Two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}

	assert(head_watches.size()>nb);

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

	pAgg ae = new SumAgg(boundsign, boundsign==LOWERBOUND ? max+1 : min, head, pSet(sets[maptype[SUM]][setid-1]));
	ae->setOptimAgg(); //FIXME temporary solution
	aggregates.push_back(ae);
	head_watches[var(head)] = ae;


	if (verbosity() >= 3) {
		reportf("Added sum minimization: Minimize ");
		printAggrExpr(ae);
		reportf("\n");
	}

	return true;
}

/*
 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
 */
bool AggSolver::maxAggAsSAT(HdEq sem, Bound boundsign, Weight bound, const Lit& head, const AggSet& set) {
	vec<Lit> clause;

	bool notunsat = true;

	if (sem==DEF) {
		for (lwlv::const_reverse_iterator i = set.getWL().rbegin(); i< set.getWL().rend() && (*i).getWeight() >= bound; i++) {
			if ((*i).getWeight() == bound && boundsign==LOWERBOUND) {
				break;
			}
			if (boundsign==LOWERBOUND) {
				clause.push(~(*i).getLit());
			} else {
				clause.push((*i).getLit());
			}
		}
		notunsat = getPCSolver()->addRule(boundsign, head, clause);
	} else {
		clause.push(boundsign==LOWERBOUND ? head : ~head);
		for (lwlv::const_reverse_iterator i = set.getWL().rbegin(); i< set.getWL().rend() && (*i).getWeight() >= bound; i++) {
			if ((*i).getWeight() == bound && boundsign==LOWERBOUND) {
				break;
			}
			clause.push((*i).getLit());
		}
		notunsat = getPCSolver()->addClause(clause);
		for (lwlv::const_reverse_iterator i =set.getWL().rbegin(); notunsat && i< set.getWL().rend() && (*i).getWeight() >= bound; i++) {
			if ((*i).getWeight() == bound && boundsign==LOWERBOUND) {
				break;
			}
			clause.clear();
			clause.push(boundsign==LOWERBOUND ? ~head : head);
			clause.push(~(*i).getLit());
			notunsat = getPCSolver()->addClause(clause);
		}
	}

	return notunsat;
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
rClause AggSolver::notifySATsolverOfPropagation(const Lit& p, AggrReason* ar) {
	//FIXME FIXME!
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
			Aggrs::printAggrExpr(ar->getAgg());
		}
		AggrReason* old_ar = aggr_reason[var(p)];
		aggr_reason[var(p)] = ar;
		rClause confl = getExplanation(p);
		getPCSolver()->addLearnedClause(confl);

		aggr_reason[var(p)] = old_ar;
		delete ar;

		return confl;
	} else if (value(p) == l_Undef) {
		if (verbosity() >= 2) {
			reportf("Deriving ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			Aggrs::printAggrExpr(ar->getAgg());
		}
		assert(aggr_reason[var(p)]==NULL);
		aggr_reason[var(p)] = ar;
		getPCSolver()->setTrue(p);
	} else {
		delete ar;
	}
	return nullPtrClause;
}

/**
 * Returns non-owning pointer
 */
rClause AggSolver::Aggr_propagate(const Lit& p) {
	rClause confl = nullPtrClause;

	if (verbosity() >= 2) {
		reportf("Aggr_propagate(");
		gprintLit(p, l_True);
		reportf(").\n");
	}

	pAgg pa = head_watches[var(p)];
	if (pa != NULL) {
		confl = pa->propagateHead(p);
	}

	vector<AggrWatch>& ws = aggr_watches[var(p)];
	for (vector<AggrWatch>::const_iterator i = ws.begin(); confl==nullPtrClause && i<ws.end(); i++) {
		confl = (*i).getSet()->propagate(p, (*i));
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
	assert(aggr_reason[var(p)]!=NULL);
	AggrReason& ar = *aggr_reason[var(p)];

	//get the explanation from the aggregate expression
	vec<Lit> lits;
	lits.push(p);

	getExplanation(ar.getAgg(), lits, ar);

	//create a conflict clause and return it
	rClause c = getPCSolver()->createClause(lits, true);
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
void AggSolver::doBacktrack(const Lit& l) {
	if (aggr_reason[var(l)] != NULL) {
		delete aggr_reason[var(l)];
		aggr_reason[var(l)] = NULL;
	}

	pAgg pa = head_watches[var(l)];
	if (pa != NULL) {
		pa->backtrackHead();
	}

	vector<AggrWatch>& vcw = aggr_watches[var(l)];
	for (vector<AggrWatch>::const_iterator i = vcw.begin(); i < vcw.end(); i++) {
		(*i).getSet()->backtrack((*i).getIndex());
	}
}

/*****************
 * IDSOLVER PART *
 *****************/

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		have not been added already(seen[A]==1 for A, seen[A]==2 for ~A)
 * 		might help to make the expression true (monotone literals!)
 */
void AggSolver::addExternalLiterals(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen) {
	pAgg agg = getAggWithHeadOccurence(v);

	for (lwlv::const_iterator i = agg->getSet()->getWL().begin(); i < agg->getSet()->getWL().end(); ++i) {
		Lit l = (*i).getLit();
		if (agg->isMonotone(*i) && ufs.find(var(l)) == ufs.end() && seen[var(l)]!=(isPositive(l)?2:1)
				&& isFalse(l)) { //TODO deze laatste voorwaarde is een HACK: eigenlijk moeten de voorwaarden zo zijn, dat enkel relevant literals worden toegevoegd, maar momenteel worden er ook literals toegevoegd die nooit in een justification zullen zitten
			assert(isFalse(l));
			loopf.push(l);
			seen[var(l)] = isPositive(l)?2:1;
		}
		//TODO en neem er zoveel monotone niet zodat ze met de ufs erbij het agg nog true kunnen maken, maar zonder niet
	}
}

vector<Var> AggSolver::getHeadsOfAggrInWhichOccurs(Var x) {
	vector<Var> heads;
	for (vector<pSet>::const_iterator i = network[x].begin(); i < network[x].end(); i++) {
		for (lsagg::const_iterator j = (*i)->getAgg().begin(); j < (*i)->getAgg().end(); j++) {
			heads.push_back(var((*j)->getHead()));
		}
	}
	return heads;
}

lwlv::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggWithHeadOccurence(x)->getSet()->getWL().begin();
}

lwlv::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggWithHeadOccurence(x)->getSet()->getWL().end();
}

void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, vec<Var>& currentjust) {
	for (vector<pSet>::const_iterator i = network[var(w)].begin(); i< network[var(w)].end(); i++) {
		pSet set = (*i);
		for (lsagg::const_iterator j = set->getAgg().begin(); j < set->getAgg().end(); j++) {
			pAgg expr = (*j);
			if (expr->getHeadValue() == l_False) {
				//reportf(" => head is false %d\n", gprintVar(var(expr->getHead())));
				continue;
			}

			//WRONG WRONG
			//If not monotone, then the head can never become true by w
			/*if(!expr->isMonotone((*(set->getWLBegin()+(*i).getIndex())))){
				reportf(" => occurence is not monotone in agg %d \n", gprintVar(var(expr->getHead())));
				continue;
			}*/

			//reportf("=> checking agg %d \n", gprintVar(var(expr->getHead())));

			Var head = var(expr->getHead());
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf;
				vec<Var> nonjstf;
				if (expr->canJustifyHead(jstf, nonjstf, currentjust, false)) {
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
	getAggWithHeadOccurence(head)->canJustifyHead(outjstf, nonjstf,	currentjust, true);
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	return getAggWithHeadOccurence(v)->canJustifyHead(jstf, nonjstf, currentjust, false);
}

///////
// OPTIMIZATION
///////

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head) {
	pAgg a = head_watches[head];
	pSet s = a->getSet();

	reportf("Current optimum: %s\n", printWeight(s->getCC()).c_str());

	if (a->isLower()) {
		a->setLowerBound(s->getCC() - 1);
	} else if (a->isUpper()) {
		a->setUpperBound(s->getCC() - 1);
	}

	if (s->getBestPossible() == s->getCC()) {
		return true;
	}

	dynamic_cast<SumAgg*> (a)->getMinimExplan(invalidation);

	return false;
}

/**
 * FIXME: not really beautiful solution, maybe it can be fixed with ASSUMPTIONS?
 * This method has to be called after every temporary solution has been found to force the propagation of
 * the newly adapted bound.
 */
void AggSolver::propagateMnmz(Var head) {
	dynamic_cast<SumAgg*> (head_watches[head])->propagateHead(true);
}
