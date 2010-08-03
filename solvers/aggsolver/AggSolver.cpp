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

AggSolver::AggSolver(pPCSolver s): ISolver(s) {}

AggSolver::~AggSolver() {
	deleteList<Agg>(aggregates);
	deleteList<AggrSet>(aggrmaxsets);
	deleteList<AggrSet>(aggrminsets);
	deleteList<AggrSet>(aggrsumsets);
	deleteList<AggrSet>(aggrprodsets);
	deleteList<AggrReason>(aggr_reason);
}

void AggSolver::removeHeadWatch(Var x){
	head_watches[x] = NULL;
	getPCSolver()->removeAggrHead(x);
}

void AggSolver::notifyVarAdded(uint64_t nvars){
	assert(head_watches.size()<nvars);
	head_watches.resize(nvars, NULL);
	assert(head_watches.size()==nvars);
	aggr_watches.resize(nvars);
	aggr_reason.resize(nvars, NULL);

	assert(head_watches.back()==NULL);
}

inline pAgg AggSolver::getAggWithHeadOccurence(Var v) const{
	assert(head_watches[v]!=NULL);
	return head_watches[v];
}

bool AggSolver::finishECNF_DataStructures() {
	notifyInitialized();

	if (getPCSolver()->modes().verbosity >= 1){
		reportf("| Number of minimum exprs.: %4zu",aggrminsets.size());
		reportf("| Number of maximum exprs.: %4zu",aggrmaxsets.size());
		reportf("| Number of sum     exprs.: %4zu",aggrsumsets.size());
		reportf("| Number of product exprs.: %4zu",aggrprodsets.size());
	}

	if (aggrminsets.size() == 0) {
		return false;
	}

	if(getPCSolver()->modes().verbosity >=1){
		int total_nb_set_lits = 0;
		int nb_sets = aggrminsets.size() + aggrmaxsets.size() + aggrsumsets.size() + aggrprodsets.size();
		for (vector<int>::size_type i = 0; i < aggrminsets.size(); i++){
			total_nb_set_lits += aggrminsets[i]->size();
		}
		for (vector<int>::size_type i = 0; i < aggrmaxsets.size(); i++){
			total_nb_set_lits += aggrmaxsets[i]->size();
		}
		for (vector<int>::size_type i = 0; i < aggrsumsets.size(); i++){
			total_nb_set_lits += aggrsumsets[i]->size();
		}
		for (vector<int>::size_type i = 0; i < aggrprodsets.size(); i++){
			total_nb_set_lits += aggrprodsets[i]->size();
		}
		reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",nb_sets,(double)total_nb_set_lits/(double)(nb_sets));
	}

	for(vector<pAgg>::const_iterator i=aggregates.begin(); i<aggregates.end(); i++){
		//FIXME dit is eigenlijk echt lelijk, zou liefst in de constructor van agg staan
		(*i)->addAggToSet();
	}

	if(getPCSolver()->modes().verbosity>=3){
		reportf("Initializing all sets:\n");
	}
	if(!finishSets(aggrminsets)){ return false; }
	if(!finishSets(aggrmaxsets)){ return false; }
	if(!finishSets(aggrsumsets)){ return false; }
	if(!finishSets(aggrprodsets)){ return false; }

	if(getPCSolver()->modes().verbosity>=3){
		int counter = 0;
		for(vector<vector<AggrWatch> >::const_iterator i=aggr_watches.begin(); i<aggr_watches.end(); i++,counter++){
			reportf("Watches of var %d:\n", gprintVar(counter));
			if(head_watches[counter]!=NULL){
				reportf("HEADwatch = ");Aggrs::printAggrExpr(head_watches[counter]);
			}
			for(vector<AggrWatch>::const_iterator j=(*i).begin(); j<(*i).end(); j++){
				Aggrs::printAggrSet((*j).getSet(), true);
			}
		}
	}

	if(getPCSolver()->modes().verbosity>=3){
		reportf("Initializing finished.\n");
	}

	if (aggrminsets.size() == 0 && aggrmaxsets.size() == 0 && aggrsumsets.size() == 0 && aggrprodsets.size() == 0) {
		return false;
	}

	return true;
}

bool AggSolver::finishSets(vector<pSet>& sets){
	for(vector<pSet>::iterator i=sets.begin(); i<sets.end(); ){
		pSet s = *i;
		if(s->nbAgg()==0){
			delete *i;
			i = sets.erase(i);
			if(getPCSolver()->modes().verbosity>=3){
				reportf("Set is deleted.\n");
			}
		}else{
			bool notunsat = s->initialize();
			if(!notunsat){
				return false;
			}
			if(s->nbAgg()==0){
				delete *i;
				i = sets.erase(i);
				if(getPCSolver()->modes().verbosity>=3){
					reportf("Set is empty after initialization, so deleted.\n");
				}
			}else{
				int index = 0;
				for (lwlv::const_iterator j = s->getWLBegin(); j < s->getWLEnd(); j++, index++){
					aggr_watches[var((*j).getLit())].push_back(AggrWatch(pSet(s), index, sign((*j).getLit()) ? NEG : POS));
				}
				i++;
			}
		}
	}
	return true;

	if(getPCSolver()->modes().verbosity>=3){
		for(vector<pSet>::iterator i=sets.begin(); i<sets.end(); i++){
			pSet s = *i;
			for(lsagg::const_iterator j=s->getAggBegin(); j<s->getAggEnd(); j++){
				Aggrs::printAggrExpr(*j);
			}
		}
	}
}

bool AggSolver::addSet(int setid, const vec<Lit>& lits, const vector<Weight>& weights) {
	assert(setid>0);
	uint64_t setindex = setid-1;
	if(lits.size()==0){
		char s[100]; sprintf(s, "Set nr. %d is empty.\n",setid);
		throw idpexception(s);
	}
	if(aggrminsets.size()>setindex && aggrminsets[setindex]!=NULL && aggrminsets[setindex]->size()!=0){
		char s[100]; sprintf(s, "Set nr. %d is defined more than once.\n",setid);
		throw idpexception(s);
	}

	vector<Weight> weights2; //inverted weights to handle minimum as maximum
	for(vector<Weight>::const_iterator i=weights.begin(); i<weights.end(); i++){
#ifdef INTWEIGHT
		if(*i == INT_MAX || *i == INT_MIN){
			throw idpexception("Weights equal to or larger than the largest integer number are not allowed in limited precision.\n");
		}
#endif
		weights2.push_back(-Weight(*i));
	}

	if(getPCSolver()->modes().verbosity>=5){
		reportf("Added set %d: ", setid);
		vector<Weight>::const_iterator w=weights.begin();
		for(int i=0; i<lits.size(); i++,w++){
			reportf("%d=%s, ", gprintVar(var(lits[i])), printWeight(*w).c_str());
		}
		reportf("\n");
	}

	while(aggrminsets.size()<=setindex){
		aggrmaxsets.push_back(new AggrMaxSet(lits, weights, this));
		aggrsumsets.push_back(new AggrSumSet(lits, weights, this));
		aggrprodsets.push_back(new AggrProdSet(lits, weights, this));
		aggrminsets.push_back(new AggrMaxSet(lits, weights2, this));
	}

	return true;
}

bool AggSolver::addAggrExpr(Var headv, int setid, Weight bound, bool lower, AggrType type, bool defined) {
	if (((vector<int>::size_type)setid) > aggrminsets.size() || aggrminsets[setid-1]==NULL || aggrminsets[setid-1]->size()==0) {
		char s[100]; sprintf(s, "Set nr. %d is used, but not defined yet.\n",setid);
		throw idpexception(s);
	}

	assert(headv>-1);
	uint64_t nb = headv;

	//INVARIANT: it has to be guaranteed that there is a watch on ALL heads
	if(head_watches.size()>nb && head_watches[headv]!=NULL){
		char s[100]; sprintf(s, "Two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}

	assert(head_watches.size()>nb);

	/*while(head_watches.size()<headv+1){
		head_watches.push_back(pAgg(pAgg()));
	}*/

	//the head of the aggregate
	Lit head = mkLit(headv, false);
	getPCSolver()->varBumpActivity(var(head)); // These guys ought to be initially a bit more important then the rest.

	assert(setid>0);
	int setindex = setid-1;

	//add if really useful varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.

	Bound b = lower?LOWERBOUND:UPPERBOUND;

	pAgg ae;
	switch(type){
	case MIN:
		//return maxAggAsSAT(defined, !lower, -bound, head, *aggrminsets[setindex]);
		b = (b==LOWERBOUND?UPPERBOUND:LOWERBOUND);
		ae = pAgg(new MaxAgg(b, -bound, head, pSet(aggrminsets[setindex])));
		break;
	case MAX:
		//return maxAggAsSAT(defined, lower, bound, head, *aggrmaxsets[setindex]);
		ae = pAgg(new MaxAgg(b, bound, head, pSet(aggrmaxsets[setindex])));
		break;
	case CARD:
#ifdef DEBUG
		for(int i=0; i<aggrsumsets[setindex]->size(); i++){
			if(aggrsumsets[setindex]->operator [](i).getWeight()!=1){
				reportf("Cardinality was loaded with wrong weights");
			}
		}
#endif
	case SUM:{
		/*bool allone = true;
		for(lwlv::const_iterator i=aggrsumsets[setindex]->getWLBegin(); allone && i<aggrsumsets[setindex]->getWLEnd(); i++){
			if((*i).getWeight()!=1){
				allone = false;
			}
		}
		if(allone){
			ae = pAgg(new CardAgg(b, bound, head, pSet(aggrsumsets[setindex])));
		}else{*/
			ae = pAgg(new SumAgg(b, bound, head, pSet(aggrsumsets[setindex])));
		//}
		break;
	}case PROD:
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for(lwlv::const_iterator i=aggrprodsets[setindex]->getWLBegin(); i<aggrprodsets[setindex]->getWLEnd(); i++){
			if((*i).getWeight() < 1){
				char s[200];
				sprintf(s, "Error: Set nr. %d contains a 0 (zero) or negative weight %s, which cannot "
						"be used in combination with a product aggregate\n",
						setid, printWeight((*i).getWeight()).c_str());
				throw idpexception(s);
			}
		}
		ae = pAgg(new ProdAgg(b, bound, head, pSet(aggrprodsets[setindex])));
		break;
	default:
		assert(false);
		throw idpexception("Only aggregates MIN, MAX, SUM or PROD are allowed in the solver.\n");
	}

	head_watches[var(head)] = pAgg(ae);

	if(defined){ //add as definition to use definition semantics
		//notify the id solver that a new aggregate definition has been added
		getPCSolver()->notifyAggrHead(var(head));
	}

	aggregates.push_back(ae);

	if(getPCSolver()->modes().verbosity>=5){
		//reportf("Added %s aggregate with head %d on set %d, %s %s of type %s.\n", defined?"defined":"completion", gprintVar(headv), setid, lower?"AGG<=":"AGG>=", bigIntegerToString(bound).c_str(), ae->getSet()->getName().c_str());
		reportf("Added %s aggregate with head %d on set %d, %s %s of type %s.\n", defined?"defined":"completion", gprintVar(headv), setid, lower?"AGG <=":"AGG >=", printWeight(bound).c_str(), ae->getSet()->getName().c_str());
	}

	return true;
}

//FIXME no optimizations should take place on mnmz aggregates (partially helped by separate add method).
//FIXME 2 more optimization should/could take place on other aggregates
bool AggSolver::addMnmzSum(Var headv, int setid, bool lower) {
	if (((vector<int>::size_type)setid) > aggrminsets.size() || aggrminsets[setid-1]==NULL || aggrminsets[setid-1]->size()==0) {
		char s[100]; sprintf(s, "Set nr. %d is used, but not defined yet.\n",setid);
		throw idpexception(s);
	}

	assert(headv>0);
	uint64_t nb = headv;

	if(head_watches.size()>nb && head_watches[headv]!=NULL){
		char s[100]; sprintf(s, "Two aggregates have the same head(%d).\n", gprintVar(headv));
		throw idpexception(s);
	}

	assert(head_watches.size()>nb);
	/*while(head_watches.size()<headv+1){
		head_watches.push_back(pAgg(pAgg()));
	}*/

	//the head of the aggregate
	Lit head = mkLit(headv, false);
	assert(setid>0);

	Bound b = lower?LOWERBOUND:UPPERBOUND;
	pAgg ae = new SumAgg(b, lower?INT_MAX:INT_MIN, head, pSet(aggrsumsets[setid-1]));
	ae->setOptimAgg(); //FIXME temporary solution
	aggregates.push_back(ae);
	head_watches[var(head)] = ae;

	return true;
}

/*
 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
 */
bool AggSolver::maxAggAsSAT(bool defined, bool lower, Weight bound, const Lit& head, const AggrSet& set){
	vec<Lit> clause;

	bool notunsat = true;

	if(defined){
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			if(lower){
				clause.push(~(*i).getLit());
			}else{
				clause.push((*i).getLit());
			}
		}
		notunsat = getPCSolver()->addRule(lower, head, clause);
	}else{
		clause.push(lower?head:~head);
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			clause.push((*i).getLit());
		}
		notunsat = getPCSolver()->addClause(clause);
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); notunsat && i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			clause.clear();
			clause.push(lower?~head:head);
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

	//This strongly improves the performance of some benchmarks, e.g. FastFood. For Hanoi it has no effect
	getPCSolver()->varBumpActivity(var(p));	//mss nog meer afhankelijk van het AANTAL sets waar het in voorkomt?

	if (getPCSolver()->value(p) == l_False) {
		if (getPCSolver()->modes().verbosity >= 2) {
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
	} else if (getPCSolver()->value(p) == l_Undef) {
		if (getPCSolver()->modes().verbosity >= 2) {
			reportf("Deriving ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			Aggrs::printAggrExpr(ar->getAgg());
		}
		assert(aggr_reason[var(p)]==NULL);
		aggr_reason[var(p)] = ar;
		getPCSolver()->setTrue(p);
	} else{
		delete ar;
	}
	return nullPtrClause;
}

/**
 * Returns non-owning pointer
 */
rClause AggSolver::Aggr_propagate(const Lit& p) {
	rClause confl = nullPtrClause;

	vector<AggrWatch>& ws = aggr_watches[var(p)];
	pAgg pa = head_watches[var(p)];

	if (getPCSolver()->modes().verbosity >= 2 && (ws.size() > 0 || pa !=NULL)){
		reportf("Aggr_propagate(");
		gprintLit(p, l_True);
		reportf(").\n");
	}

	if(pa!=NULL){
		confl = pa->propagateHead(p);
	}
	for (vector<AggrWatch>::const_iterator i = ws.begin(); confl == nullPtrClause && i < ws.end(); i++) {
		confl = (*i).getSet()->propagate(p, (*i));
	}
	return confl;
}

rClause AggSolver::getExplanation(const Lit& p) {
	assert(aggr_reason[var(p)]!=NULL);
	AggrReason& ar = *aggr_reason[var(p)];

	//get the explanation from the aggregate expression
	vec<Lit> lits;
	lits.push(p);

	ar.getAgg()->getExplanation(lits, ar);

	//create a conflict clause and return it
	rClause c = getPCSolver()->makeClause(lits, true);

	if (getPCSolver()->modes().verbosity >= 2) {
		reportf("Implicit reason clause for ");
		gprintLit(p, sign(p)?l_False:l_True); reportf(" : ");
		Print::printClause(c, getPCSolver());
		reportf("\n");
	}

	return c;
}

/**
 * Not viable to backtrack a certain number of literals, unless also tracking whether a literal was propagated in
 * which solvers when a conflict occurred
 */
void AggSolver::doBacktrack(const Lit& l){
	if (aggr_reason[var(l)] != NULL) {
		delete aggr_reason[var(l)];
		aggr_reason[var(l)] = NULL;
	}

	pAgg pa = head_watches[var(l)];
	if(pa!=NULL){
		pa->backtrackHead();
	}

	vector<AggrWatch>& vcw = aggr_watches[var(l)];
	for(vector<AggrWatch>::const_iterator i=vcw.begin(); i<vcw.end(); i++){
		pSet set = (*i).getSet();
		//currently, the same literal can still occur in head and body, which causes propagation
		//(and backtrack) twice for the same literal in the same expression
		//using this method, it is possible that they are backtracked in a different order than the watch list,
		//but this should be no problem

		//second condition ensures that only backtracking is done if the value was indeed propagated in the set
		if(set->getStackSize()!=0 && var(set->getStackBack().getLit())==var(l)){
			set->backtrack((*i).getIndex());
		}
	}
}

/*****************
 * IDSOLVER PART *
 *****************/

void AggSolver::createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	getAggWithHeadOccurence(v)->createLoopFormula(ufs, loopf, seen);
}

void AggSolver::getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads){
	vector<AggrWatch>& w = aggr_watches[x];
	for(vector<AggrWatch>::const_iterator i=w.begin(); i<w.end(); i++){
		pSet s = (*i).getSet();
		for(lsagg::const_iterator j=s->getAggBegin(); j<s->getAggEnd(); j++){
			heads.push(var((*j)->getHead()));
		}
	}
}

lwlv::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggWithHeadOccurence(x)->getSet()->getWLBegin();
}

lwlv::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggWithHeadOccurence(x)->getSet()->getWLEnd();
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in heads, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, vec<int> &currentjust){
	for (vector<AggrWatch>::const_iterator i = aggr_watches[var(w)].begin(); i < aggr_watches[var(w)].end(); i++) {
		pSet set = (*i).getSet();
		for(lsagg::const_iterator j=set->getAggBegin(); j<set->getAggEnd(); j++){
			pAgg expr = (*j);
			if(expr->getHeadValue() == l_False){ continue; }

			Var head = var(expr->getHead());
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf; vec<Var> nonjstf;
				if(expr->canJustifyHead(jstf, nonjstf, currentjust, false)){
					currentjust[head]=0;
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
 * and return true if the justification is external (maybe this is better checked in the IDsolver).
 */
bool AggSolver::findJustificationAggr(Var head, vec<Lit>& jstf){
	vec<Var> nonjstf;
	vec<int> currentjust;
	return getAggWithHeadOccurence(head)->canJustifyHead(jstf, nonjstf, currentjust, true);
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust){
	return getAggWithHeadOccurence(v)->canJustifyHead(jstf, nonjstf, currentjust, false);
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head){
	pAgg a = head_watches[head];
	pSet s = a->getSet();

	reportf("Current optimum: %s\n", printWeight(s->getCC()).c_str());

	if(a->isLower()){
		a->setLowerBound(s->getCC() - 1);
	}else if(a->isUpper()){
		a->setUpperBound(s->getCC() - 1);
	}


	if(s->getBestPossible()==s->getCC()){
		return true;
	}

	dynamic_cast<SumAgg*>(a)->getMinimExplan(invalidation);

	return false;
}

/**
 * FIXME: not really beautiful solution, maybe it can be fixed with ASSUMPTIONS?
 * This method has to be called after every temporary solution has been found to force the propagation of
 * the newly adapted bound.
 */
void AggSolver::propagateMnmz(Var head){
	dynamic_cast<SumAgg*>(head_watches[head])->propagateHead(true);
}
