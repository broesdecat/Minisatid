#include "AggSolver.h"
#include <algorithm>

AggSolver* AggSolver::aggsolver;

AggSolver::AggSolver() :
	init(true) {
	AggSolver::aggsolver = this;
}

AggSolver::~AggSolver() {
}

void AggSolver::notifyVarAdded(){
	head_watches.push(NULL);
	aggr_watches.push();
	aggr_reason.push(NULL);
}

inline Agg& AggSolver::getAggWithHeadOccurence(Var v) const{
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
	if(s->nbAgg()==0){
		delete s;
	}else{
		s->initialize();
		int index = 0;
		for (lwlv::const_iterator i = s->getWLBegin(); i < s->getWLEnd(); i++, index++){
			aggr_watches[var((*i).getLit())].push(AggrWatch(s, index, sign((*i).getLit()) ? NEG : POS));
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

	//vec<Weight> weights2; //inverted weights to handle minimum as maximum
	vector<Weight> weights2;
	for(vector<Weight>::iterator i=weights.begin(); i<weights.end(); i++){
		weights2.push_back(-Weight(*i));

		//Required by the weight klasse om overflow te kunnen checken
		if (*i < 0) {
			reportf("Error: Set nr. %d contains a negative weight, %s.\n",set_id,bigIntegerToString(*i).c_str()), exit(3);
		}
	}

	while(aggrminsets.size()<=setindex){
		aggrmaxsets.push_back(new AggrMaxSet(lits, weights));
		aggrsumsets.push_back(new AggrSumSet(lits, weights));
		aggrprodsets.push_back(new AggrProdSet(lits, weights));
		aggrminsets.push_back(new AggrMaxSet(lits, weights2));
	}
}

/*
 * For a maximum: if lower,  head <=> conj of negation of all literals with weight higher than bound
 * 				  if higher, head <=> disj of all literals with weight higher/eq than bound
 *
 * IMPORTANT: counting down on vectors cannot check for i>= 0, because the type is UNSIGNED!
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
		idsolver->addRule(lower, clause);
	}else{
		clause.push(lower?head:~head);
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			clause.push((*i).getLit());
		}
		solver->addClause(clause);
		for(lwlv::const_reverse_iterator i=set.getWLRBegin(); i<set.getWLREnd() && (*i).getWeight()>=bound; i++){
			if((*i).getWeight()==bound && lower){
				break;
			}
			clause.clear();
			clause.push(lower?~head:head);
			clause.push(~(*i).getLit());
			solver->addClause(clause);
		}
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

	head_watches.growTo(headv+1);

	//the head of the aggregate
	Lit head = Lit(headv, false);
	assert(setid>0);
	uint setindex = setid-1;

	//add if really useful varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.

	Agg* ae;
	switch(type){
	case MIN:
		//maxAggAsSAT(defined, !lower, -bound, head, *aggrminsets[setindex]);
		//return;
		ae = new MaxAgg(!lower, -bound, head, aggrminsets[setindex]);
		break;
	case MAX:
		//maxAggAsSAT(defined, lower, bound, head, *aggrmaxsets[setindex]);
		//return;
		ae = new MaxAgg(lower, bound, head, aggrmaxsets[setindex]);
		break;
	case SUM:
		ae = new SumAgg(lower, bound, head, aggrsumsets[setindex]);
		break;
	case PROD:
		//NOTE this can be solved by taking 0 out of the set and making the necessary transformations
		// p <=> a <= prod{l1=0, l2=2} can be replaced with p <=> a <= prod{l2=2} & l1~=0 if a is strictly positive
		for(vector<int>::size_type i=0; i<aggrprodsets[setindex]->size(); i++){
			if(aggrprodsets[setindex]->operator [](i).getWeight()==0){
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

	head_watches[var(head)] = ae;

	if(defined){ //add as definition to use definition semantics
		//notify the id solver that a new aggregate definition has been added
		idsolver->notifyAggrHead(var(head));
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

	head_watches.growTo(headv+1);

	//the head of the aggregate
	Lit head = Lit(headv, false);
	assert(setid>0);
	uint setindex = setid-1;

	Agg* ae = new SumAgg(lower, lower?INT_MAX:INT_MIN, head, aggrsumsets[setindex]);
	head_watches[var(head)] = ae;
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
	if (solver->value(p) == l_False) {
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
			int litlevel = solver->getLevel(var(confl->operator [](i)));
			if (litlevel > lvl){
				lvl = litlevel;
			}
		}
		solver->backtrackTo(lvl);

		if(confl->size()>1){
			solver->addLearnedClause(confl);
		}
		aggr_reason[var(p)] = old_ar;
		return confl;
	} else if (solver->value(p) == l_Undef) {
		if (verbosity >= 2) {
			reportf("Deriving ");
			gprintLit(p, l_True);
			reportf(" because of the aggregate expression ");
			printAggrExpr(ar->getAgg());
		}
		aggr_reason[var(p)] = ar;
		solver->setTrue(p);
	} else{
		delete ar;
	}
	return NULL;
}

Clause* AggSolver::Aggr_propagate(const Lit& p) {
	Clause* confl = NULL;
	vec<AggrWatch>& ws = aggr_watches[var(p)];
	if (verbosity >= 2 && ws.size() > 0){
		reportf("Aggr_propagate(");
		gprintLit(p, l_True);
		reportf(").\n");
	}
	if(head_watches[var(p)]!=NULL){
		confl = head_watches[var(p)]->propagateHead(p);
	}
	for (int i = 0; confl == NULL && i < ws.size(); i++) {
		confl = ws[i].getSet()->propagate(p, ws[i]);
	}
	return confl;
}

Clause* AggSolver::getExplanation(const Lit& p) {
	vec<Lit> lits;
	lits.push(p);
	AggrReason& ar = *aggr_reason[var(p)];

	//get the explanation from the aggregate expression
	ar.getAgg().getExplanation(lits, ar);

	//create a conflict clause and return it
	Clause* c = Clause_new(lits, true);

	if (verbosity >= 2) {
		reportf("Implicit reason clause for ");
		gprintLit(p, sign(p)?l_False:l_True); reportf(" : "); solver->printClause(*c); reportf("\n");
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

	if(head_watches[var(l)]!=NULL){
		head_watches[var(l)]->backtrackHead();
	}

	vec<AggrWatch>& vcw = aggr_watches[var(l)];
	for(int i=0; i<vcw.size(); i++){
		AggrSet* set = vcw[i].getSet();
		//currently, the same literal can still occur in head and body, which causes propagation
		//(and backtrack) twice for the same literal in the same expression
		//using this method, it is possible that they are backtracked in a different order than the watch list,
		//but this should be no problem

		//second condition ensures that only backtracking is done if the value was indeed propagated in the set
		if(set->getStackSize()!=0 && var(set->getStackBack().getLit())==var(l)){
			set->backtrack(vcw[i].getIndex());
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
		for(lagg::const_iterator j=w[i].getSet()->getAggBegin(); j<w[i].getSet()->getAggEnd(); j++){
			heads.push(var((*j)->getHead()));
		}
	}
}

lwlv::const_iterator AggSolver::getAggLiteralsBegin(Var x) const {
	return getAggWithHeadOccurence(x).getSet()->getWLBegin();
}

lwlv::const_iterator AggSolver::getAggLiteralsEnd(Var x) const {
	return getAggWithHeadOccurence(x).getSet()->getWLEnd();
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
		for(lagg::const_iterator j=aw.getSet()->getAggBegin(); j<aw.getSet()->getAggEnd(); j++){
			Agg& expr = **j;
			if(expr.getHeadValue() == l_False){ continue; }

			Var head = var(expr.getHead());
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
void AggSolver::findCycleSources(const Agg& v) const{
	vec<Lit> nj;
	v.becomesCycleSource(nj);
	idsolver->cycleSourceAggr(var(v.getHead()), nj);
}

bool AggSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust){
	Agg& expr = aggsolver->getAggWithHeadOccurence(v);
	return expr.canJustifyHead(jstf, nonjstf, currentjust, false);
}

bool AggSolver::invalidateSum(vec<Lit>& invalidation, Var head){
	SumAgg* a = dynamic_cast<SumAgg*>(head_watches[head]);

	if(verbosity>0){
		reportf("Current optimum: %s\n", bigIntegerToString(a->getSet()->getCC()).c_str());
	}

	a->setBound(a->getSet()->getCC() + 1);

	if(a->getSet()->getBestPossible()==a->getSet()->getCC()){
		return true;
	}

	a->getMinimExplan(invalidation);

	return false;
}

/**
 * FIXME:
 * has to be called after each solution has been found, just before starting to search
 */
void AggSolver::propagateMnmz(Var head){
	SumAgg* a = dynamic_cast<SumAgg*>(head_watches[head]);
	a->propagateHead(true);
}

//=================================================================================================
// Debug + etc:

void AggSolver::printAggrExpr(const Agg& ae){
	gprintLit(ae.getHead(), ae.getHeadValue());
	const AggrSet* set = ae.getSet();
	if(ae.isLower()){
		reportf(" <- %s{", set->getName().c_str());
	}else{
		reportf(" <- %s <= %s{", bigIntegerToString(ae.getBound()).c_str(), set->getName().c_str());
	}
	for (lwlv::const_iterator i=set->getWLBegin(); i<set->getWLEnd(); ++i) {
		reportf(" "); gprintLit((*i).getLit(), (*i).getValue()); reportf("(%s)",bigIntegerToString((*i).getWeight()).c_str());
	}
	if(ae.isLower()){
		reportf(" } <= %s. Known values: bestcertain=%s, bestpossible=%s\n", bigIntegerToString(ae.getBound()).c_str(), bigIntegerToString(set->getCC()).c_str(), bigIntegerToString(set->getCP()).c_str());
	}else{
		reportf(" }. Known values: bestcertain=%s, bestpossible=%s\n", bigIntegerToString(set->getCC()).c_str(), bigIntegerToString(set->getCP()).c_str());
	}
}
