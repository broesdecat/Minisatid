#include "AggSolver.h"
#include <algorithm>

AggSolver* AggSolver::aggsolver;

AggSolver::AggSolver() :
	init(true), empty(false) {
	AggSolver::aggsolver = this;
}

AggSolver::~AggSolver() {
}

void AggSolver::notifyVarAdded(){
	aggr_watches.push();
	aggr_reason.push();
}

inline AggrWatch& AggSolver::getWatchOfHeadOccurence(Var v){
	return aggr_watches[v][0];
}

bool AggSolver::finishECNF_DataStructures() {
	init = false;

	if (verbosity >= 1){
		reportf("| Number of aggregate exprs.: %4d",aggr_exprs.size());
	}

	if (aggr_exprs.size() == 0) {
		return false;
	}

	if(verbosity >=1){
		int total_nb_set_lits = 0;
		for (int i = 0; i < aggr_sets.size(); i++){
			total_nb_set_lits += aggr_sets[i]->wlitset.size();
		}
		reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",aggr_sets.size(),(double)total_nb_set_lits/(double)(aggr_sets.size()));
	}

	//initialize all counters
	for(int i=0; i<aggr_exprs.size(); i++){
		aggr_exprs[i]->initialize();
	}

	return true;
}

void AggSolver::addSet(int set_id, vec<Lit>& lits, vec<int>& weights) {
	int setindex = set_id-1;
	if(lits.size()==0){
		reportf("Error: Set nr. %d is empty.\n",set_id), exit(3);
	}
	if(aggr_sets.size()>setindex && aggr_sets[setindex]!=NULL && aggr_sets[setindex]->wlitset.size()!=0){
		reportf("Error: Set nr. %d is defined more then once.\n",set_id), exit(3);
	}
	assert(lits.size()==weights.size());

	while(aggr_sets.size()<=setindex){
		aggr_sets.push(new AggrSet());
	}
	AggrSet& set = *aggr_sets[setindex];

	for (int i = 0; i < lits.size(); i++) {
		if (weights[i] < 0) {
			reportf("Error: Set nr. %d contains a negative weight, %d.\n",set_id,weights[i]), exit(3);
		}
		set.wlitset.push_back(WLit(lits[i], weights[i]));
	}
	sort(set.wlitset.begin(), set.wlitset.end());
}

void AggSolver::addAggrExpr(int defn, int setid, int bound, bool lower, AggrType type) {
	if (setid > aggr_sets.size() || aggr_sets[setid-1]==NULL || aggr_sets[setid-1]->wlitset.size()==0) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",setid), exit(3);
	}

	//the head of the aggregate
	Lit head = Lit(defn, false);
	int setindex = setid-1;

	//add if really useful varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.

	Agg* ae;
	switch(type){
	case MIN:
		ae = new MinAgg(lower, bound, head, aggr_sets[setindex]);
		break;
	case MAX:
		ae = new MaxAgg(lower, bound, head, aggr_sets[setindex]);
		break;
	case SUM:
		ae = new SPAgg(lower, bound, head, aggr_sets[setindex], true);
		break;
	case PROD:
		//TODO this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for(vector<int>::size_type i=0; i<aggr_sets[setindex]->wlitset.size(); i++){
			if(aggr_sets[setindex]->wlitset[i].weight==0){
				reportf("Error: Set nr. %d contains a 0 (zero) weight, which cannot "
						"be used in combination with a product aggregate\n", setid), exit(3);
			}
		}
		ae = new SPAgg(lower, bound, head, aggr_sets[setindex], false);
		break;
	default:
		assert(false);
	}
	aggr_exprs.push(ae);

	//This step guarantees the invariant that the head occurence of var(l) is always the first element of the watches of var(l)
	if(aggr_watches[var(head)].size()>0){
		assert(aggr_watches[var(head)][0].type!=HEAD);
		AggrWatch w = aggr_watches[var(head)][0];
		aggr_watches[var(head)][0] = AggrWatch(ae, -1, HEAD);
		aggr_watches[var(head)].push(w);
	}else{
		aggr_watches[var(head)].push(AggrWatch(ae, -1, HEAD));
	}
	assert(aggr_watches[var(head)][0].type==HEAD);

	for (vector<int>::size_type i = 0; i < ae->set->wlitset.size(); i++){
		aggr_watches[var(ae->set->wlitset[i].lit)].push(AggrWatch(ae, i, sign(ae->set->wlitset[i].lit) ? NEG : POS));
	}

	//notify the id solver that a new aggregate definition has been added
	idsolver->notifyAggrHead(var(head));
}

/**
 * The method propagates the fact that p has been derived to the SAT solver. If a conflict occurs,
 * a conflict clause is returned. Otherwise, the value is set to true in the sat solver.
 *
 * @pre: literal p can be derived to be true because of the given aggregate reason
 *
 * @remarks: only method allowed to use the sat solver datastructures
 */
Clause* AggSolver::notifySATsolverOfPropagation(Lit p, AggrReason* ar) {
	if (verbosity >= 2) {
		reportf("%seriving ", solver->value(p)==l_True ? "Again d" : "D");
		printLit(p, solver->value(p));
		reportf(" because of the aggregate expression ");
		printAggrExpr(*(ar->expr));
	}

	if (solver->value(p) == l_False) {
		if (verbosity >= 2){
			reportf("Conflict.\n");
		}
		AggrReason* old_ar = aggr_reason[var(p)];
		aggr_reason[var(p)] = ar;
		Clause* confl = getExplanation(p);
		solver->addLearnedClause(confl);
		aggr_reason[var(p)] = old_ar;
		return confl;
	} else if (solver->value(p) == l_Undef) {
		aggr_reason[var(p)] = ar;
		solver->setTrue(p);
	} else{
		delete ar;
	}
	return NULL;
}

Clause* AggSolver::Aggr_propagate(Lit p) {
	Clause* confl = NULL;
	vec<AggrWatch>& ws = aggr_watches[var(p)];
	if (verbosity >= 2 && ws.size() > 0){
		reportf("Aggr_propagate(%s%d).\n",sign(p)?"-":"",var(p)+1);
	}
	for (int i = 0; confl == NULL && i < ws.size(); i++) {
		confl = (*ws[i].expr).propagate(p, ws[i]);
	}
	return confl;
}

Clause* AggSolver::getExplanation(Lit p) {
	vec<Lit> lits;
	lits.push(p);
	AggrReason& ar = *aggr_reason[var(p)];

	//get the explanation from the aggregate expression
	ar.expr->getExplanation(p, lits, ar);

	//create a conflict clause and return it
	Clause* c = Clause_new(lits, true);

	if (verbosity >= 2) {
		reportf("Implicit reason clause for ");
		printLit(p, !sign(p)); reportf(" : "); solver->printClause(*c); reportf("\n");
	}

	return c;
}

void AggSolver::doBacktrack(Lit l){
	if (aggr_reason[var(l)] != NULL) {
		delete aggr_reason[var(l)];
		aggr_reason[var(l)] = NULL;
	}

	vec<AggrWatch>& vcw = aggr_watches[var(l)];
	for(int i=0; i<vcw.size(); i++){
		Agg& ae = *vcw[i].expr;
		if(ae.stack.size()!=0 && var(ae.stack.last().wlit.lit)==var(l)){
			ae.backtrack(vcw[i].type, vcw[i].index);
		}
	}
}

/*****************
 * IDSOLVER PART *
 *****************/

//FIXME debug the idsolver part

void AggSolver::createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	getWatchOfHeadOccurence(v).expr->createLoopFormula(ufs, loopf, seen);
}

void AggSolver::getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads){
	vec<AggrWatch>& w = aggr_watches[x];
	for(int i=0; i<w.size(); i++){
		heads.push(var(w[i].expr->head));
	}
}

void AggSolver::getLiteralsOfAggr(Var x, vec<Lit>& lits){
	vector<WLit>& ll = getWatchOfHeadOccurence(x).expr->set->wlitset;
	for(vector<WLit>::size_type i=0; i<ll.size(); i++){
		lits.push(ll[i].lit);
	}
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in lits, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Var w, vec<vec<Lit> >& jstf, vec<Var>& lits, vec<int> &nb_body_lits_to_justify){
	for (int i = 0; i < aggr_watches[w].size(); ++i) {
		AggrWatch& aw = (aggr_watches[w])[i];
		if(aw.type == HEAD){ continue; }
		if(aw.expr->headvalue == l_False){ continue; }

		Var head = var(aw.expr->head);
		if (nb_body_lits_to_justify[head] > 0) { //only check its body for justification when it has not yet been derived
			vec<Lit> newjust;
			aw.expr->propagateJustifications(newjust, nb_body_lits_to_justify);
			if(nb_body_lits_to_justify[head]==0){ //head has now been derived
				lits.push(head);
				jstf.push();
				newjust.copyTo(jstf.last());
			}
		}
	}
}

/**
 * This is called when l has been recently assigned (became true), so all aggregates with ~l in the body and part
 * of the justification may have become cycle sources
 */
void AggSolver::findCycleSourcesFromBody(Lit l){
	vec<AggrWatch>& as = aggr_watches[var(l)];
	if(as.size()==0){ return; }

	int j=0;
	if(as[0].type==HEAD){ //the head does not have to be checked
		j = 1;
	}
	for (; j < as.size(); j++) { // ~l is possibly used in the head atom's cf_justification.
		AggrWatch& aw = as[j];
		if (aw.expr->headvalue != l_False && !idsolver->isCS[var(aw.expr->head)]) {
			vec<Lit>& cf = idsolver->getCFJustificationAggr(var(aw.expr->head));
			bool alltrue = true;
			for(int i=0; alltrue && i<cf.size(); i++){
				if(cf[i] == ~l){ // ~l is indeed used in the cf_justification.
					alltrue = false;
				}
			}
			if(!alltrue){
				findCycleSources(aw);
			}
		}
	}
}

/**
 * Checks whether the CF justification of l is still valid (no elements have become false)
 */
void AggSolver::findCycleSourcesFromHead(Var v){
	AggrWatch& aw = getWatchOfHeadOccurence(v);
	if (aw.expr->headvalue == l_False || idsolver->isCS[v]){
		return;
	}
	vec<Lit>& cf = idsolver->getCFJustificationAggr(v);
	bool alltrue = true;
	for(int i=0; alltrue && i<cf.size(); i++){
		if(solver->value(cf[i]) == l_False){ // There is a false literal in the cf_justification.
			alltrue = false;
		}
	}
	if(!alltrue){
		findCycleSources(aw);
	}
}

/*
 * Precondition: V is of type AGGR. Its head is non-false, and its cf_justification does not support it.
 * If a justification can be found that is non-false and does not depend on any literal in the same scc,
 * than the justification is changed. Otherwise, it is added as a cycle source.
 */
void AggSolver::findCycleSources(AggrWatch& v){
	vec<Lit> nj; // New sp_justification.
	v.expr->becomesCycleSource(nj);

	idsolver->cycleSourceAggr(var(v.expr->head), nj);
}

bool AggSolver::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc){
	AggrWatch& aw = aggsolver->getWatchOfHeadOccurence(v);
	return aw.expr->directlyJustifiable(v, ufs, q, j, seen, scc);
}

//=================================================================================================
// Debug + etc:

//TODO these can be inlined if they are not used in Agg
void AggSolver::printLit(Lit l, lbool value) {
	reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value == l_True ? '1' : (value == l_False ? '0' : 'X'));
}

void AggSolver::printAggrExpr(const Agg& ae){
	printLit(ae.head, ae.headvalue);
	if(ae.lower){
		reportf(" <- %s{", ae.name.c_str());
	}else{
		reportf(" <- %d <= %s{", ae.bound, ae.name.c_str());
	}
	for (vector<int>::size_type i=0; i<ae.set->wlitset.size(); ++i) {
		reportf(" "); printLit(ae.set->wlitset[i].lit, ae.litvalue[i]); reportf("(%d)",ae.set->wlitset[i].weight);
	}
	if(ae.lower){
		reportf(" } <= %d. Known values: bestcertain=%d, bestpossible=%d\n", ae.bound, ae.currentbestcertain, ae.currentbestpossible);
	}else{
		reportf(" }. Known values: bestcertain=%d, bestpossible=%d\n", ae.currentbestcertain, ae.currentbestpossible);
	}
}
