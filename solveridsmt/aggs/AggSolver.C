#include "AggSolver.h"

#include "Solver.h"
#include "IDSolver.h"

#include "Agg.h"
#include "AggSets.h"

typedef shared_ptr<IDSolver> pIDSolver;
typedef weak_ptr<IDSolver> wpIDSolver;
typedef shared_ptr<AggSolver> pAggSolver;
typedef weak_ptr<AggSolver> wpAggSolver;
typedef shared_ptr<Solver> pSolver;
typedef weak_ptr<Solver> wpSolver;


#include <algorithm>

AggSolver::AggSolver() :
	init(true) {}

AggSolver::~AggSolver() {
	deleteList<Agg>(aggregates);
	deleteList<AggrSet>(aggrmaxsets);
	deleteList<AggrSet>(aggrminsets);
	deleteList<AggrSet>(aggrsumsets);
	deleteList<AggrSet>(aggrprodsets);
	deleteList<AggrReason>(aggr_reason);
}

void AggSolver::remove(){
	getSolver()->resetAggSolver();
	getSolver().reset();
	getIDSolver().reset();
	//FIXME: prevent from using a solver after it has been removed
}

void AggSolver::notifyVarAdded(int nvars){
	head_watches.resize(nvars);
	aggr_watches.resize(nvars);
	aggr_reason.resize(nvars);

	//head_watches.push_back(pAgg(pAgg()));
	assert(head_watches.back()==NULL);
	//aggr_watches.push_back(vector<AggrWatch>());
	//aggr_reason.push_back(NULL);
}

inline pAgg AggSolver::getAggWithHeadOccurence(Var v) const{
	assert(head_watches[v]!=NULL);
	return head_watches[v];
}

bool AggSolver::finishECNF_DataStructures() {
	init = false;

	if (verbosity >= 1){
		reportf("| Number of minimum exprs.: %4d",aggrminsets.size());
		reportf("| Number of maximum exprs.: %4d",aggrmaxsets.size());
		reportf("| Number of sum     exprs.: %4d",aggrsumsets.size());
		reportf("| Number of product exprs.: %4d",aggrprodsets.size());
	}

	if (aggrminsets.size() == 0) {
		return false;
	}

	if(verbosity >=1){
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

	finishSets(aggrminsets);
	finishSets(aggrmaxsets);
	finishSets(aggrsumsets);
	finishSets(aggrprodsets);

	if (aggrminsets.size() == 0 && aggrmaxsets.size() == 0 && aggrsumsets.size() == 0 && aggrprodsets.size() == 0) {
		return false;
	}

	return true;
}

void AggSolver::finishSets(vector<pSet>& sets){
	for(vector<pSet>::iterator i=sets.begin(); i<sets.end(); i++){
		pSet s = *i;
		if(s->nbAgg()==0){
			delete *i;
			sets.erase(i);
		}else{
			s->initialize();
			int index = 0;
			for (lwlv::const_iterator i = s->getWLBegin(); i < s->getWLEnd(); i++, index++){
				aggr_watches[var((*i).getLit())].push_back(AggrWatch(pSet(s), index, sign((*i).getLit()) ? NEG : POS));
			}
			for(lsagg::const_iterator i=s->getAggBegin(); i<s->getAggEnd(); i++){
				(*i)->initialize();
			}
		}
	}
}

void AggSolver::addSet(int set_id, vec<Lit>& lits, vector<Weight>& weights) {
	assert(set_id>0);
	uint setindex = set_id-1;
	if(lits.size()==0){
		reportf("Error: Set nr. %d is empty.\n",set_id), exit(3);
	}
	if(aggrminsets.size()>setindex && aggrminsets[setindex]!=NULL && aggrminsets[setindex]->size()!=0){
		reportf("Error: Set nr. %d is defined more than once.\n",set_id), exit(3);
	}

	vector<Weight> weights2; //inverted weights to handle minimum as maximum
	for(vector<Weight>::iterator i=weights.begin(); i<weights.end(); i++){
		if (*i < 0) {
			reportf("Error: Set nr. %d contains a negative weight, %s.\n",set_id,bigIntegerToString(*i).c_str()), exit(3);
		}

		weights2.push_back(-Weight(*i));

	}

	if(verbosity>=5){
		reportf("Added set %d: ", set_id);
		vector<Weight>::iterator w=weights.begin();
		for(int i=0; i<lits.size(); i++,w++){
			reportf("%d=%s, ", gprintVar(var(lits[i])), bigIntegerToString(*w).c_str());
		}
		reportf("\n");
	}

	weak_ptr<AggSolver> wpAggSolver(shared_from_this());
	while(aggrminsets.size()<=setindex){
		aggrmaxsets.push_back(new AggrMaxSet(lits, weights, wpAggSolver));
		aggrsumsets.push_back(new AggrSumSet(lits, weights, wpAggSolver));
		aggrprodsets.push_back(new AggrProdSet(lits, weights, wpAggSolver));
		aggrminsets.push_back(new AggrMaxSet(lits, weights2, wpAggSolver));
	}
}

void AggSolver::addAggrExpr(Var headv, int setid, Weight bound, bool lower, AggrType type, bool defined) {
	if (((vector<int>::size_type)setid) > aggrminsets.size() || aggrminsets[setid-1]==NULL || aggrminsets[setid-1]->size()==0) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",setid), exit(3);
	}

	//INVARIANT: it has to be guaranteed that there is a watch on ALL heads
	if(head_watches.size()>headv && head_watches[headv]!=NULL){
		reportf("Error: Two aggregates have the same head(%d).\n", gprintVar(headv)), exit(3);
	}

	while(head_watches.size()<headv+1){
		head_watches.push_back(pAgg(pAgg()));
	}

	//the head of the aggregate
	Lit head = Lit(headv, false);
	assert(setid>0);
	uint setindex = setid-1;

	//add if really useful varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.

	pAgg ae;
	switch(type){
	case MIN:
		//maxAggAsSAT(defined, !lower, -bound, head, *aggrminsets[setindex]);
		//return;
		ae = pAgg(new MaxAgg(!lower, -bound, head, pSet(aggrminsets[setindex])));
		break;
	case MAX:
		//maxAggAsSAT(defined, lower, bound, head, *aggrmaxsets[setindex]);
		//return;
		ae = pAgg(new MaxAgg(lower, bound, head, pSet(aggrmaxsets[setindex])));
		break;
	case SUM:
		ae = pAgg(new SumAgg(lower, bound, head, pSet(aggrsumsets[setindex])));
		break;
	case PROD:
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for(lwlv::const_iterator i=aggrprodsets[setindex]->getWLBegin(); i<aggrprodsets[setindex]->getWLEnd(); i++){
			if((*i).getWeight()==0){
				reportf("Error: Set nr. %d contains a 0 (zero) weight, which cannot "
						"be used in combination with a product aggregate\n", setid), exit(3);
			}
		}
		ae = pAgg(new ProdAgg(lower, bound, head, pSet(aggrprodsets[setindex])));
		break;
	default:
		assert(false);
		reportf("Only aggregates MIN, MAX, SUM or PROD are allowed in the solver.\n");
		exit(3);
	}

	head_watches[var(head)] = pAgg(ae);

	if(defined){ //add as definition to use definition semantics
		//notify the id solver that a new aggregate definition has been added
		getIDSolver()->notifyAggrHead(var(head));
	}

	aggregates.push_back(ae);

	if(verbosity>=5){
		reportf("Added %s aggregate with head %d on set %d, %s %s of type %s.\n", defined?"defined":"completion", gprintVar(headv), setid, lower?"AGG<=":"AGG>=", bigIntegerToString(bound).c_str(), ae->getSet()->getName().c_str());
	}
}

//FIXME no optimizations should take place on mnmz aggregates (partially helped by separate add method).
//FIXME 2 more optimization should/could take place on other aggregates
void AggSolver::addMnmzSum(Var headv, int setid, bool lower) {
	if (((vector<int>::size_type)setid) > aggrminsets.size() || aggrminsets[setid-1]==NULL || aggrminsets[setid-1]->size()==0) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",setid), exit(3);
	}

	if(head_watches.size()>headv && head_watches[headv]!=NULL){
		reportf("Error: Two aggregates have the same head(%d).\n", gprintVar(headv)), exit(3);
	}

	while(head_watches.size()<headv+1){
		head_watches.push_back(pAgg(pAgg()));
	}

	//the head of the aggregate
	Lit head = Lit(headv, false);
	assert(setid>0);
	uint setindex = setid-1;

	pAgg ae = new SumAgg(lower, lower?INT_MAX:INT_MIN, head, pSet(aggrsumsets[setindex]));
	aggregates.push_back(ae);
	head_watches[var(head)] = ae;
}

/*
 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
 */
void AggSolver::maxAggAsSAT(bool defined, bool lower, Weight bound, const Lit& head, const AggrSet& set){
	vec<Lit> clause;

	if(defined){
		clause.push(head);
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
		getIDSolver()->addRule(lower, clause);
	}else{
		clause.push(lower?head:~head);
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			clause.push((*i).getLit());
		}
		getSolver()->addClause(clause);
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			clause.clear();
			clause.push(lower?~head:head);
			clause.push(~(*i).getLit());
			getSolver()->addClause(clause);
		}
	}
}

/**
 * The method propagates the fact that p has been derived to the SAT solver. If a conflict occurs,
 * a conflict clause is returned. Otherwise, the value is set to true in the sat solver.
 *
 * @pre: literal p can be derived to be true because of the given aggregate reason
 *
 * @remarks: only method allowed to use the sat solver datastructures
 */
Clause* AggSolver::notifySATsolverOfPropagation(const Lit& p, AggrReason* ar) {
	if (getSolver()->value(p) == l_False) {
		if (verbosity >= 2) {
			reportf("Deriving conflict in ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			printAggrExpr(ar->getAgg());
		}
		AggrReason* old_ar = aggr_reason[var(p)];
		aggr_reason[var(p)] = ar;
		Clause* confl = getExplanation(p);

		/*
		 * Due to current (TODO this can be avoided) incomplete propagation, the conflict should possibly
		 * have been derived at an earlier level. So check for this and first backtrack to that level.
		 */
		int lvl = 0;
		for (int i = 1; i < confl->size(); i++){
			int litlevel = getSolver()->getLevel(var(confl->operator [](i)));
			if (litlevel > lvl){
				lvl = litlevel;
			}
		}
		getSolver()->backtrackTo(lvl);

		if(confl->size()>1){
			getSolver()->addLearnedClause(confl);
		}

		aggr_reason[var(p)] = old_ar;
		delete ar;

		return confl;
	} else if (getSolver()->value(p) == l_Undef) {
		if (verbosity >= 2) {
			reportf("Deriving ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			printAggrExpr(ar->getAgg());
		}
		assert(aggr_reason[var(p)]==NULL);
		aggr_reason[var(p)] = ar;
		getSolver()->setTrue(p);
	} else{
		delete ar;
	}
	return NULL;
}

Clause* AggSolver::Aggr_propagate(const Lit& p) {
	Clause* confl = NULL;
	vector<AggrWatch>& ws = aggr_watches[var(p)];
	if (verbosity >= 2 && ws.size() > 0){
		reportf("Aggr_propagate(");
		gprintLit(p, l_True);
		reportf(").\n");
	}

	pAgg pa = head_watches[var(p)];
	if(pa!=NULL){
		confl = pa->propagateHead(p);
	}
	for (vector<AggrWatch>::const_iterator i = ws.begin(); confl == NULL && i < ws.end(); i++) {
		confl = (*i).getSet()->propagate(p, (*i));
	}
	return confl;
}

Clause* AggSolver::getExplanation(const Lit& p) {
	assert(aggr_reason[var(p)]!=NULL);
	AggrReason& ar = *aggr_reason[var(p)];

	//get the explanation from the aggregate expression
	vec<Lit> lits;
	lits.push(p);

	ar.getAgg()->getExplanation(lits, ar);

	//create a conflict clause and return it
	Clause* c = Clause_new(lits, true);

	if (verbosity >= 2) {
		reportf("Implicit reason clause for ");
		gprintLit(p, sign(p)?l_False:l_True); reportf(" : "); getSolver()->printClause(*c); reportf("\n");
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
					heads.push(Lit(head, false));
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

	if(verbosity>0){
		reportf("Current optimum: %s\n", bigIntegerToString(s->getCC()).c_str());
	}

	a->setBound(s->getCC() + 1);

	if(s->getBestPossible()==s->getCC()){
		return true;
	}

	dynamic_cast<SumAgg*>(a)->getMinimExplan(invalidation);

	return false;
}

/**
 * FIXME:
 * has to be called after each solution has been found, just before starting to search
 */
void AggSolver::propagateMnmz(Var head){
	dynamic_cast<SumAgg*>(head_watches[head])->propagateHead(true);
}

void AggSolver::printAggrExpr(pAgg ae){
	gprintLit(ae->getHead(), ae->getHeadValue());
	pSet set = ae->getSet();
	if(ae->isLower()){
		reportf(" <- %s{", set->getName().c_str());
	}else{
		reportf(" <- %s <= %s{", bigIntegerToString(ae->getBound()).c_str(), set->getName().c_str());
	}
	for (lwlv::const_iterator i=set->getWLBegin(); i<set->getWLEnd(); ++i) {
		reportf(" "); gprintLit((*i).getLit(), (*i).getValue()); reportf("(%s)",bigIntegerToString((*i).getWeight()).c_str());
	}
	if(ae->isLower()){
		reportf(" } <= %s. Known values: bestcertain=%s, bestpossible=%s\n", bigIntegerToString(ae->getBound()).c_str(), bigIntegerToString(set->getCC()).c_str(), bigIntegerToString(set->getCP()).c_str());
	}else{
		reportf(" }. Known values: bestcertain=%s, bestpossible=%s\n", bigIntegerToString(set->getCC()).c_str(), bigIntegerToString(set->getCP()).c_str());
	}
}
