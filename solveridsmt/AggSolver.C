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
	head_watches.push(NULL);
	aggr_watches.push();
	aggr_reason.push(NULL);
}

inline Agg& AggSolver::getAggWithHeadOccurence(Var v){
	assert(head_watches[v]!=NULL);
	return *head_watches[v];
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
			total_nb_set_lits += aggrminsets[i]->wlits.size();
		}
		for (vector<int>::size_type i = 0; i < aggrmaxsets.size(); i++){
			total_nb_set_lits += aggrmaxsets[i]->wlits.size();
		}
		for (vector<int>::size_type i = 0; i < aggrsumsets.size(); i++){
			total_nb_set_lits += aggrsumsets[i]->wlits.size();
		}
		for (vector<int>::size_type i = 0; i < aggrprodsets.size(); i++){
			total_nb_set_lits += aggrprodsets[i]->wlits.size();
		}
		reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",nb_sets,(double)total_nb_set_lits/(double)(nb_sets));
	}

	int nbsets = aggrminsets.size();
	for(int i=0; i<nbsets; i++){
		finishSets(aggrminsets[i]);
		finishSets(aggrmaxsets[i]);
		finishSets(aggrsumsets[i]);
		finishSets(aggrprodsets[i]);
	}

	if (aggrminsets.size() == 0 && aggrmaxsets.size() == 0 && aggrsumsets.size() == 0 && aggrprodsets.size() == 0) {
		return false;
	}

	return true;
}

void AggSolver::finishSets(AggrSet* s){
	if(s->aggregates.size()==0){
		delete s;
	}else{
		s->initialize();
		for (vector<int>::size_type i = 0; i < s->wlits.size(); i++){
			aggr_watches[var(s->wlits[i].lit)].push(AggrWatch(s, i, sign(s->wlits[i].lit) ? NEG : POS));
		}
	}
}

void AggSolver::addSet(int set_id, vec<Lit>& lits, vec<int>& weights) {
	assert(set_id>0);
	uint setindex = set_id-1;
	if(lits.size()==0){
		reportf("Error: Set nr. %d is empty.\n",set_id), exit(3);
	}
	if(aggrminsets.size()>setindex && aggrminsets[setindex]!=NULL && aggrminsets[setindex]->wlits.size()!=0){
		reportf("Error: Set nr. %d is defined more then once.\n",set_id), exit(3);
	}
	for(int i=0; i<weights.size(); i++){
		if (weights[i] < 0) {
			reportf("Error: Set nr. %d contains a negative weight, %d.\n",set_id,weights[i]), exit(3);
		}
	}

	//TODO: add checks for bound lower than maxint and higher than minint

	assert(lits.size()==weights.size());

	while(aggrminsets.size()<=setindex){
		aggrminsets.push_back(new AggrMinSet(lits, weights));
		aggrmaxsets.push_back(new AggrMaxSet(lits, weights));
		aggrsumsets.push_back(new AggrSumSet(lits, weights));
		aggrprodsets.push_back(new AggrProdSet(lits, weights));
	}
}

/*
 * Two methods for doing reduction of min and max aggregates right to SAT(ID)
 * The main disadvantage of the method is when the same set is used very often (like in optimization problems, where
 * you will have one atom for the set being equal to each possible value) and there is few possibility of real optimizations there
 */
/*
 * For a minimum: if lower,  head <=> disj of all literals with weight lower/eq than bound
 * 				  if higher, head <=> conj of negation of all literals with weight lower than bound
 */
void AggSolver::addMinAgg(bool defined, bool lower, int bound, Lit head, AggrSet& set){
	vec<Lit> clause;

	if(defined){
		clause.push(head);
		for(vector<int>::size_type i=0; i<set.wlits.size() && set.wlits[i].weight<=bound; i++){
			if(set.wlits[i].weight==bound && !lower){
				break;
			}
			if(lower){
				clause.push(set.wlits[i].lit);
			}else{
				clause.push(~set.wlits[i].lit);
			}
		}
		idsolver->addRule(!lower, clause);
	}else{
		clause.push(lower?~head:head);
		for(vector<int>::size_type i=0; i<set.wlits.size() && set.wlits[i].weight<=bound; i++){
			if(set.wlits[i].weight==bound && !lower){
				break;
			}
			clause.push(set.wlits[i].lit);
		}
		solver->addClause(clause);
		for(vector<int>::size_type i=0; i<set.wlits.size() && set.wlits[i].weight<=bound; i++){
			if(set.wlits[i].weight==bound && !lower){
				break;
			}
			clause.clear();
			clause.push(lower?head:~head);
			clause.push(~set.wlits[i].lit);
			solver->addClause(clause);
		}
	}
}

/*
 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
 */
void AggSolver::addMaxAgg(bool defined, bool lower, int bound, Lit head, AggrSet& set){
	vec<Lit> clause;

	if(defined){
		clause.push(head);
		for(vector<int>::size_type i=set.wlits.size()-1; set.wlits[i].weight>=bound; i--){
			if(i==0 || (set.wlits[i].weight==bound && lower)){
				break;
			}
			if(lower){
				clause.push(~set.wlits[i].lit);
			}else{
				clause.push(set.wlits[i].lit);
			}
		}
		idsolver->addRule(lower, clause);
	}else{
		clause.push(lower?head:~head);
		for(vector<int>::size_type i=set.wlits.size()-1; set.wlits[i].weight>=bound; i--){
			if(i==0 || (set.wlits[i].weight==bound && lower)){
				break;
			}
			clause.push(set.wlits[i].lit);
		}
		solver->addClause(clause);
		for(vector<int>::size_type i=set.wlits.size()-1; set.wlits[i].weight>=bound; i--){
			if(i==0 || (set.wlits[i].weight==bound && lower)){
				break;
			}
			clause.clear();
			clause.push(lower?~head:head);
			clause.push(~set.wlits[i].lit);
			solver->addClause(clause);
		}
	}
}

void AggSolver::addAggrExpr(Var headv, int setid, int bound, bool lower, AggrType type, bool defined) {
	if (((vector<int>::size_type)setid) > aggrminsets.size() || aggrminsets[setid-1]==NULL || aggrminsets[setid-1]->wlits.size()==0) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",setid), exit(3);
	}

	head_watches.growTo(headv+1);

	//INVARIANT: it has to be guaranteed that there is a watch on ALL heads
	if(head_watches[headv]!=NULL){
		reportf("Error: Two aggregates have the same head(%d).\n",headv+1), exit(3);
	}

	//the head of the aggregate
	Lit head = Lit(headv, false);
	assert(setid>0);
	uint setindex = setid-1;

	//add if really useful varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.

	Agg* ae;
	switch(type){
	case MIN:
		//addMinAgg(defined, lower, bound, head, *aggr_sets[setindex]);
		//return;
		ae = new MinAgg(lower, bound, head, aggrminsets[setindex]);
		break;
	case MAX:
		//addMaxAgg(defined, lower, bound, head, *aggr_sets[setindex]);
		//return;
		ae = new MaxAgg(lower, bound, head, aggrmaxsets[setindex]);
		break;
	case SUM:
		ae = new SumAgg(lower, bound, head, aggrsumsets[setindex]);
		break;
	case PROD:
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for(vector<int>::size_type i=0; i<aggrprodsets[setindex]->wlits.size(); i++){
			if(aggrprodsets[setindex]->wlits[i].weight==0){
				reportf("Error: Set nr. %d contains a 0 (zero) weight, which cannot "
						"be used in combination with a product aggregate\n", setid), exit(3);
			}
		}
		ae = new ProdAgg(lower, bound, head, aggrprodsets[setindex]);
		break;
	default:
		assert(false);
		reportf("Only aggregates MIN, MAX, SUM or PROD are allowed in the solver.\n");
		exit(3);
	}
	aggr_exprs++;

	//FIXME: de behandeling van deze head watches overal verspreiden (naast aggr_watches deze ook gebruiken, of
	//afh van de situatie zelfs alleen deze)!
	//FIXME 2: maar 1 datastructuur voor de verschillende soorten sets (en de type safety wat verminderen)
	//FIXME 3: in het aggregaat zelf dan opslaan wat de size was van de stack toen de head afgeleid werd
	head_watches[var(head)] = ae;

	if(defined){ //add as definition to use definition semantics
		//notify the id solver that a new aggregate definition has been added
		idsolver->notifyAggrHead(var(head));
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
Clause* AggSolver::notifySATsolverOfPropagation(Lit p, AggrReason* ar) {
	if (verbosity >= 2) {
		reportf("Deriving ");
		printLit(p, l_True);
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
		if(confl->size()>1){
			solver->addLearnedClause(confl);
		}
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
	if(head_watches[var(p)]!=NULL){
		confl = head_watches[var(p)]->propagateHead(p);
	}
	for (int i = 0; confl == NULL && i < ws.size(); i++) {
		confl = (*ws[i].set).propagate(p, ws[i]);
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

	if(head_watches[var(l)]!=NULL){
		head_watches[var(l)]->backtrackHead();
	}

	vec<AggrWatch>& vcw = aggr_watches[var(l)];
	for(int i=0; i<vcw.size(); i++){
		AggrSet& set = *vcw[i].set;
		//currently, the same literal can still occur in head and body, which causes propagation
		//(and backtrack) twice for the same literal in the same expression
		//using this method, it is possible that they are backtracked in a different order than the watch list,
		//but this should be no problem

		//second condition ensures that only backtracking is done if the value was indeed propagated in the set
		if(set.stack.size()!=0 && var(set.stack.back().wlit.lit)==var(l)){
			set.backtrack(vcw[i].index);
		}
	}
}

/*****************
 * IDSOLVER PART *
 *****************/

void AggSolver::createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen){
	Agg& expr = getAggWithHeadOccurence(v);
	expr.createLoopFormula(ufs, loopf, seen);
}

void AggSolver::getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads){
	vec<AggrWatch>& w = aggr_watches[x];
	for(int i=0; i<w.size(); i++){
		for(vector<int>::size_type j=0; j<w[i].set->aggregates.size(); j++){
			heads.push(var(w[i].set->aggregates[j]->head));
		}
	}
}

vector<WLV>& AggSolver::getLiteralsOfAggr(Var x){
	return getAggWithHeadOccurence(x).set->wlits;
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
		for(vector<int>::size_type j=0; j<aw.set->aggregates.size(); j++){
			Agg& expr = *aw.set->aggregates[j];
			if(expr.headvalue == l_False){ continue; }

			Var head = var(expr.head);
			if (currentjust[head] > 0) { //only check its body for justification when it has not yet been derived
				vec<Lit> jstf; vec<Var> nonjstf;
				if(expr.canJustifyHead(jstf, nonjstf, currentjust, false)){
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
	Agg& expr = aggsolver->getAggWithHeadOccurence(head);
	vec<Var> nonjstf;
	vec<int> currentjust;
	return expr.canJustifyHead(jstf, nonjstf, currentjust, true);
}

/*
 * V is not false so find a justification for it. Preferably find one that does not involve loops.
 * If a justification is found, but it contains loops, v is added as a cycle source
 */
void AggSolver::findCycleSources(Agg& v){
	vec<Lit> nj;
	v.becomesCycleSource(nj);
	idsolver->cycleSourceAggr(var(v.head), nj);
}

bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust){
	Agg& expr = aggsolver->getAggWithHeadOccurence(v);
	return expr.canJustifyHead(jstf, nonjstf, currentjust, false);
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head){
	SumAgg* a = dynamic_cast<SumAgg*>(head_watches[head]);
	a->bound = a->set->currentbestcertain++;

	if(a->set->getBestPossible()==a->set->currentbestcertain){
		return true;
	}

	AggrReason* reason = new AggrReason(a, HEAD, -1);
	a->getExplanation(~a->head, invalidation, *reason);
	delete reason;

	return false;
}

//=================================================================================================
// Debug + etc:

void AggSolver::printLit(Lit l, lbool value) {
	reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value == l_True ? '1' : (value == l_False ? '0' : 'X'));
}

void AggSolver::printAggrExpr(const Agg& ae){
	printLit(ae.head, ae.headvalue);
	if(ae.lower){
		reportf(" <- %s{", ae.set->name.c_str());
	}else{
		reportf(" <- %d <= %s{", ae.bound, ae.set->name.c_str());
	}
	for (vector<int>::size_type i=0; i<ae.set->wlits.size(); ++i) {
		reportf(" "); printLit(ae.set->wlits[i].lit, ae.set->wlits[i].value); reportf("(%d)",ae.set->wlits[i].weight);
	}
	if(ae.lower){
		reportf(" } <= %d. Known values: bestcertain=%d, bestpossible=%d\n", ae.bound, ae.set->currentbestcertain, ae.set->currentbestpossible);
	}else{
		reportf(" }. Known values: bestcertain=%d, bestpossible=%d\n", ae.set->currentbestcertain, ae.set->currentbestpossible);
	}
}
