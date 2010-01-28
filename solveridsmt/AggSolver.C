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

	if(verbosity>=5){
		for(int i=0; i<aggr_watches.size(); i++){
			reportf("Watches for %d: ", i+1);
			for(int j=0; j<aggr_watches[i].size(); j++){
				solver->printLit(aggr_watches[i][j].expr->set->wlitset[aggr_watches[i][j].index].lit);
			}
			reportf("\n");
		}
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

void AggSolver::addAggrExpr(Var headv, int setid, int bound, bool lower, AggrType type) {
	if (setid > aggr_sets.size() || aggr_sets[setid-1]==NULL || aggr_sets[setid-1]->wlitset.size()==0) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",setid), exit(3);
	}
	if(aggr_watches[headv].size()>0 && aggr_watches[headv][0].type==HEAD){ //INVARIANT: it has to be guaranteed that there is a watch on ALL heads
		reportf("Error: Two aggregates have the same head(%d).\n",headv+1), exit(3);
	}

	//the head of the aggregate
	Lit head = Lit(headv, false);
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
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
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
		//currently, the same literal can still occur in head and body, which causes propagation
		//(and backtrack) twice for the same literal in the same expression
		//using this method, it is possible that they are backtracked in a different order than the watch list,
		//but this should be no problem
		if(ae.stack.size()!=0 && var(ae.stack.last().wlit.lit)==var(l)){
			ae.backtrack(vcw[i].index);
		}
	}
}

/*****************
 * IDSOLVER PART *
 *****************/

void AggSolver::createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	getWatchOfHeadOccurence(v).expr->createLoopFormula(ufs, loopf, seen);
}

void AggSolver::getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads){
	vec<AggrWatch>& w = aggr_watches[x];
	for(int i=0; i<w.size(); i++){
		heads.push(var(w[i].expr->head));
	}
}

vector<WLit>& AggSolver::getLiteralsOfAggr(Var x){
	return getWatchOfHeadOccurence(x).expr->set->wlitset;
}

/**
 * Propagates the fact that w has been justified and use the info on other earlier justifications to derive other
 * heads.
 *
 * @post: any new derived heads are in heads, with its respective justification in jstf
 */
void AggSolver::propagateJustifications(Lit w, vec<vec<Lit> >& jstfs, vec<Lit>& heads, vec<int> &currentjust){
	for (int i = 0; i < aggr_watches[var(w)].size(); ++i) {
		AggrWatch& aw = (aggr_watches[var(w)])[i];
		if(aw.type == HEAD){ continue; }
		if(aw.expr->headvalue == l_False){ continue; }

		Var head = var(aw.expr->head);
		if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
			vec<Lit> jstf; vec<Var> nonjstf;
			if(aw.expr->canJustifyHead(jstf, nonjstf, currentjust, false)){
				currentjust[head]=0;
				heads.push(Lit(head, false));
				jstfs.push();
				jstf.copyTo(jstfs.last());
			}
		}
	}
}

/**
 * The given head is not false. So it has a (possibly looping) justification. Find this justification
 * and return true if the justification is external (maybe this is better checked in the IDsolver).
 */
bool AggSolver::findJustificationAggr(Var head, vec<Lit>& jstf){
	AggrWatch& aw = aggsolver->getWatchOfHeadOccurence(head);
	vec<Var> nonjstf;
	vec<int> currentjust;
	return aw.expr->canJustifyHead(jstf, nonjstf, currentjust, true);
}

/*
 * V is not false so find a justification for it. Preferably find one that does not involve loops.
 * If a justification is found, but it contains loops, v is added as a cycle source
 */
void AggSolver::findCycleSources(AggrWatch& v){
	vec<Lit> nj;
	v.expr->becomesCycleSource(nj);

	idsolver->cycleSourceAggr(var(v.expr->head), nj);
}

bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust){
	AggrWatch& aw = aggsolver->getWatchOfHeadOccurence(v);
	return aw.expr->canJustifyHead(jstf, nonjstf, currentjust, false);
}

//=================================================================================================
// Debug + etc:

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
