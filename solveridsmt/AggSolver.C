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
	Aggr_watches.push();
	aggr_reason.push();
}

AggrWatch& AggSolver::getWatchOfHeadOccurence(Var v){
	return Aggr_watches[v][0];
}

vec<AggrWatch>& AggSolver::getWatches(Var v){
	return Aggr_watches[v];
}

bool AggSolver::finishECNF_DataStructures() {
	init = false;

	if (verbosity >= 1){
		reportf("| Number of aggregate exprs.: %4d",aggr_exprs.size());
	}

	if (aggr_exprs.size() == 0) {
		return false;
	} else {
		int total_nb_set_lits = 0;
		for (int i = 0; i < aggr_sets.size(); i++){
			total_nb_set_lits += aggr_sets[i]->wlitset.size();
		}
		if (verbosity >= 1){reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",aggr_sets.size(),(double)total_nb_set_lits/(double)(aggr_sets.size()));	}

		//initialize all counters
		for(int i=0; i<aggr_exprs.size(); i++){
			aggr_exprs[i]->initialize();
		}

		//FIXME eigenlijk alles eerst finishen, dan alles propageren, dan beginnen searchen
		//aka dus eens nadenken over solver interactie (eigenlijk blijven propageren tussen alle solvers
		//zolang er iets veranderd.

		// Now do the initial propagations based on set literals that already have a truth value.
		/*Clause * confl = NULL;
		for (int i = 0; i < solver->qhead && confl == NULL; ++i) // from qhead onwards will still be propagated by simplify().
			confl = Aggr_propagate(solver->trail[i]);
		if (confl != NULL) {
			throw theoryUNSAT;
		}*/
		return true;
	}
}

void AggSolver::addSet(int set_id, vec<Lit>& lits, vec<int>& weights) {
	int setindex = set_id-1;
	if (lits.size() == 0) {
		reportf("Error: Set nr. %d is empty,\n",set_id); exit(3);
	}
	if(aggr_sets.size()>set_id && aggr_sets[setindex]->wlitset.size()>0){
		reportf("Error: Set nr. %d is defined more then once.\n",set_id), exit(3);
	}
	assert(lits.size()==weights.size());

	while(aggr_sets.size()<set_id){
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

/**
 * Adds an aggregate expression with only one bound on it. The bound is always interpreted as lEQ or gEQ
 *
 * @PRE: no negative weights
 * 		 no double literals
 * 		 no literals occuring both positive and negative
 * 		 no 0 weights when using a product aggregate
 */
void AggSolver::addAggrExpr(int defn, int setid, int bound, bool lower, AggrType type) {
	if (setid > aggr_sets.size()) {
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
			if(aggr_sets[setindex]->wlitset[i].weight<1){
				reportf("Error: Set nr. %d contains a 0 (zero) weight, which cannot "
						"be used in combination with a product aggregate\n", setid), exit(3);
			}
		}
		ae = new SPAgg(lower, bound, head, aggr_sets[setindex], false);
		break;
	default: assert(false);break;
	}
	aggr_exprs.push(ae);

	//This step guarantees the invariant that the head occurence of var(l) is always the first element of the watches of var(l)
	if(Aggr_watches[var(head)].size()>0){
		AggrWatch w = Aggr_watches[var(head)][0];
		Aggr_watches[var(head)][0] = AggrWatch(ae, -1, HEAD);
		Aggr_watches[var(head)].push(w);
	}else{
		Aggr_watches[var(head)].push(AggrWatch(ae, -1, HEAD));
	}

	for (vector<int>::size_type i = 0; i < ae->set->wlitset.size(); i++){
		Aggr_watches[var(ae->set->wlitset[i].lit)].push(AggrWatch(ae, i, sign(ae->set->wlitset[i].lit) ? NEG : POS));
	}

	idsolver->notifyAggrHead(var(head));
}

/**
 * @PRE: literal p can be derived to be true because of the given aggregate reason
 *
 * it is then checked whether there is a conflict (construct conflict and add learned clause),
 * whether it can be propagated to the solver or whether it was already true.
 *
 * this is the only method that is allowed to check the literal values of the sat solver
 *
 * should not do any changes to the agg datastructures!
 */
Clause* AggSolver::aggrEnqueue(Lit p, AggrReason* ar) {
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
	} else
		delete ar;
	return NULL;
}

/**
 * Goes through all watches and propagates the fact that p was set true.
 */
Clause* AggSolver::Aggr_propagate(Lit p) {
	Clause* confl = NULL;
	vec<AggrWatch>& ws = Aggr_watches[var(p)];
	if (verbosity >= 2 && ws.size() > 0){
		reportf("Aggr_propagate(%s%d).\n",sign(p)?"-":"",var(p)+1);
	}
	for (int i = 0; confl == NULL && i < ws.size(); i++) {
		Agg& ae = *ws[i].expr;
		confl = ae.propagate(p, ws[i]);
	}
	return confl;
}

/*_________________________________________________________________________________________________
 |
 |  implicitReasonClause : (Lit)  ->  [Clause*]
 |
 |  Description:
 |    Use for a literal that was deduced using a aggregate expression. This method constructs,
 |    from the AggrReason stored for it, a "reason clause" usable in clause learning.
 |    This clause is saved nowhere except in the object returned. Delete it immediately
 |    after use, to avoid memory leaks.
 |________________________________________________________________________________________________@*/
Clause* AggSolver::getExplanation(Lit p) {
	vec<Lit> lits;
	lits.push(p);
	AggrReason& ar = *aggr_reason[var(p)];

	//find the index of the literal in the set that resulted in the reason.
	//Can be optimized by storing it in the reason, but usually the number of aggregate expressions it not that high.
	int i = 0;
	while (i < Aggr_watches[var(p)].size() && (&(Aggr_watches[var(p)])[i].expr->set)!= &(ar.expr->set)){
		i++;
	}
	assert(i<Aggr_watches[var(p)].size());
	int p_idx = (Aggr_watches[var(p)])[i].index;

	//get the explanation from the aggregate expression
	ar.expr->getExplanation(p, lits, p_idx, ar);

	//create a conflict clause and return it
	Clause* c = Clause_new(lits, true);
	if (verbosity >= 2) {
		reportf("Implicit reason clause for ");
		printLit(p, !sign(p)); reportf(" : "); printClause(*c); reportf("\n");
	}

	return c;
}

/**
 * Correct the min and max values of the aggregates in which l was propagated
 *
 * @PRE: backtracking is in anti-chronologous order!
 */
void AggSolver::doBacktrack(Lit l){
	if (aggr_reason[var(l)] != NULL) {
		delete aggr_reason[var(l)];
		aggr_reason[var(l)] = NULL;
	}

	vec<AggrWatch>& vcw = Aggr_watches[var(l)];
	for(int i=0; i<vcw.size(); i++){
		Agg& ae = *vcw[i].expr;
		if(ae.stack.size()!=0 && var(ae.stack.last().wlit.lit)==var(l)){
			ae.backtrack(vcw[i].type, vcw[i].index);
		}
	}
}

/*void TSolver::Subsetminimize(const vec<Lit>& lits) {
	if (!ecnf_mode.mnmz)
		reportf("ERROR! Attempt at adding a subset minimize statement, though ECNF specifiers did not contain \"mnmz\".\n"), exit(
				3);
	if (lits.size() == 0) {
		reportf("Error: The set of literals to be minimized is empty,\n");
		exit(3);
	}
	if (to_minimize.size() != 0) {
		reportf("At most one set of literals to be minimized can be given.\n");
		exit(3);
	}

	for (int i = 0; i < lits.size(); i++)
		to_minimize.push(lits[i]);
}*/

/*****************
 * IDSOLVER PART *
 *****************/

void AggSolver::createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	getWatchOfHeadOccurence(v).expr->createLoopFormula(ufs, loopf, seen);
}

void AggSolver::getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads){
	vec<AggrWatch>& w = Aggr_watches[x];
	for(int i=0; i<w.size(); i++){
		if(var(w[i].expr->head)!=x){
			heads.push(var(w[i].expr->head));
		}
	}
}

void AggSolver::getLiteralsOfAggr(Var x, vec<Lit>& lits){
	vector<WLit>& ll = getWatchOfHeadOccurence(x).expr->set->wlitset;
	for(vector<WLit>::size_type i=0; i<ll.size(); i++){
		lits.push(ll[i].lit);
	}
}

/**
 * Propagate the fact that L has a cyclefree and supporting justification
 * All new justifications are pushed onto the existing queue
 */
void AggSolver::propagateJustifications(Var l, vec<vec<Lit> >& jstf, vec<Var>& lits, vec<int> &nb_body_lits_to_justify){
	for (int i = 0; i < Aggr_watches[l].size(); ++i) {
		AggrWatch& aw = (Aggr_watches[l])[i];
		if (aw.type == HEAD){
			continue;
		}
		if(aw.expr->headvalue == l_False){
			continue;
		}
		Var v = var(aw.expr->head);
		lits.push(v);
		jstf.push();
		if (nb_body_lits_to_justify[v] > 0) {
			aw.expr->propagateJustifications(jstf.last(), nb_body_lits_to_justify);
		}
	}
}

/**
 * This is called when l has been recently assigned (became true), so all aggregates with ~l in the body and part
 * of the justification may have become cycle sources
 */
void AggSolver::findCycleSourcesFromBody(Lit l){
	vec<AggrWatch>& as = Aggr_watches[var(l)];
	if(as.size()==0){ return; }

	int j=0;
	if(as[0].type==HEAD){ //the head does not have to be checked
		j = 1;
	}
	for (; j < as.size(); j++) { // ~l is possibly used in the head atom's cf_justification.
		AggrWatch& aw = as[j];
		Lit head = aw.expr->head;
		if (aw.expr->headvalue != l_False) {
			//TODO de IDsolver gebruikt de meest recente values, de aggsolver niet, maar hier maakt het denk ik niet uit, omdat defpropagatie maar gedaan wordt na alle gewone propagaties
			//	mss een assert doen met een boolean die checkt of we wel definitiepropagatie mogen doen.
			vec<Lit>& cf = idsolver->getCFJustificationAggr(var(head));
			for (int k=0; k < cf.size(); k++){
				if(cf[k] == ~l){ // ~l is indeed used in the cf_justification.
					findCycleSources(aw);
					break;
				}
			}
		}
	}
}

/**
 * Checks whether the CF justification of l is still valid (no elements have become false)
 */
void AggSolver::findCycleSourcesFromHead(Var v){
	AggrWatch& aw = getWatchOfHeadOccurence(v);
	if (aw.expr->headvalue == l_False){ return; }
	vec<Lit>& cf = idsolver->getCFJustificationAggr(v);
	for(int i=0; i<cf.size(); i++){
		if(solver->value(cf[i]) == l_False){ // There is a false literal in the cf_justification.
			findCycleSources(aw);
			break;
		}
	}
}

/*
 * Precondition: V is of type DISJ. It is non-false, and its cf_justification does not support it.
 * Postcondition: sp_justification..[v] supports v. v is added a cycle source if necessary (i.e., if there might be a cycle through its sp_justification).
 */
void AggSolver::findCycleSources(AggrWatch& v){
	if(idsolver->isCS[var(v.expr->head)]){ return; }

	vec<Lit> nj; // New sp_justification.
	bool becomes_cycle_source = v.expr->becomesCycleSource(nj);

	idsolver->cycleSourceAggr(var(v.expr->head), nj, becomes_cycle_source);
}

bool AggSolver::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc){
	AggrWatch& aw = aggsolver->getWatchOfHeadOccurence(v);
	return aw.expr->directlyJustifiable(v, ufs, q, j, seen, scc);
}

//=================================================================================================
// Debug + etc:

inline void AggSolver::printLit(Lit l, lbool value) {
	reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value == l_True ? '1' : (value == l_False ? '0' : 'X'));
}

template<class C>
inline void AggSolver::printClause(const C& c) {
	for (int i = 0; i < c.size(); i++) {
		printLit(c[i], !sign(c[i]));
		fprintf(stderr, " ");
	}
}

inline void AggSolver::printAggrExpr(const Agg& ae){
	printLit(ae.head, ae.headvalue);
	if(ae.lower){
		reportf(" <- %s{", ae.name.c_str());
	}else{
		reportf(" <- %d <= %s{", ae.bound, ae.name.c_str());
	}
	for (vector<int>::size_type i=0; i<ae.set->wlitset.size(); ++i) {
		reportf(" "); printLit(ae.set->wlitset[i].lit, ae.setcopy[i]); reportf("(%d)",ae.set->wlitset[i].weight);
	}
	if(ae.lower){
		reportf(" } <= %d. Known values: currentbestcertain=%d, currentbestpossible=%d\n", ae.bound, ae.currentbestcertain, ae.currentbestpossible);
	}else{
		reportf(" }. Known values: currentbestcertain=%d, currentbestpossible=%d\n", ae.currentbestcertain, ae.currentbestpossible);
	}
}
