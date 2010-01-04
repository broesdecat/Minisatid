#include "AggSolver.h"

AggSolver::AggSolver() :
	init(true), empty(false) {
	AggSolver::aggsolver = this;
}

AggSolver::~AggSolver() {
}

inline lbool AggSolver::value(Var x) const {
	return solver->value(x);
}

//FIXME deze aggsolver manier is niet echt mooi (om Agg toegang te geven tot aggsolver
//en het zorgt ook dat value niet inline kan zijn hier (wat zeker niet de bedoeling is)
AggSolver* AggSolver::aggsolver;

lbool AggSolver::value(Lit p) const {
	return solver->value(p);
}
inline int AggSolver::nVars() const {
	return solver->nVars();
}

void AggSolver::notifyVarAdded(){
	Aggr_watches.push();
	aggr_reason.push();
	countedlit.push(false);
}

void AggSolver::finishECNF_DataStructures() {
	init = false;

	if (verbosity >= 1){
		reportf("| Number of aggregate exprs.: %4d",aggr_exprs.size());
	}

	if (aggr_exprs.size() == 0) {
		solver->setAggSolver(NULL);
		if (verbosity >= 1) {
			reportf("                                            |\n");
			reportf("|    (there will be no aggregate propagations)                                |\n");
		}
		return;
	} else {
		countedlit.growTo(nVars(), false);

		int total_nb_set_lits = 0;
		for (int i = 0; i < aggr_sets.size(); i++){
			total_nb_set_lits += aggr_sets[i]->wlitset.size();
		}
		if (verbosity >= 1){reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",aggr_sets.size(),(double)total_nb_set_lits/(double)(aggr_sets.size()));	}

		//initialize all counters
		for(int i=0; i<aggr_exprs.size(); i++){
			aggr_exprs[i]->initialize();
		}

		//TODO TODO TODO TODO eigenlijk alles eerst finishen, dan alles propageren, dan beginnen searchen
		// Now do the initial propagations based on set literals that already have a truth value.
		Clause * confl = NULL;
		for (int i = 0; i < solver->qhead && confl == NULL; ++i) // from qhead onwards will still be propagated by simplify().
			confl = Aggr_propagate(solver->trail[i]);
		if (confl != NULL) {
			throw theoryUNSAT;
		}
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

	//literals occurring multiple times are allowed from now in
	//FIXME if a literal occurs multiple times, the correct value has to be used, depending on the aggregate type
	//for example if MIN 3=5 3=6, then it should be 5!!!

	aggr_sets.growTo(set_id);
	AggrSet& set = *aggr_sets[setindex];

	int max = 0;
	for (int i = 0; i < lits.size(); i++) {
		if (weights[i] < 0) {
			reportf("Error: Set nr. %d contains a negative weight, %d.\n",set_id,weights[i]), exit(3);
		}
		set.wlitset.push(WLit(lits[i], weights[i]));
		max += weights[i];
	}
	qsort(set.wlitset, set.wlitset.size(), sizeof(WLit), compare_WLits);
	set.cmax = max;
}

/*
 Adds an aggregate expression with only one bound on it. The bound is always interpreted as lEQ or gEQ
 */
//TODO check if infinity should be expressible too
void AggSolver::addAggrExpr(int defn, int setid, int bound, bool lower, AggrType type) {
	if (setid > aggr_sets.size()) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",setid), exit(3);
	}

	//the head of the aggregate
	Lit c = Lit(defn, false);
	int setindex = setid-1;

	//TODObroes add if really useful varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.

	Agg* ae;
	switch(type){
	case MIN:
		ae = new MinAgg(lower, bound, c, aggr_sets[setindex]);
		break;
	case MAX:
		ae = new MaxAgg(lower, bound, c, aggr_sets[setindex]);
		break;
	case SUM:
		ae = new SumAgg(lower, bound, c, aggr_sets[setindex]);
		break;
	case PROD:
		ae = new ProdAgg(lower, bound, c, aggr_sets[setindex]);
		break;
	default: assert(false);break;
	}
	aggr_exprs.push(ae);

	AggrSet* as = aggr_sets[setindex];
	as->exprs.push(ae);

	Aggr_watches[var(c)].push(AggrWatch(ae, -1, HEAD));

	//for every literal in the litset, add a watch that points to the expressions in which it occurs
	for (int i = 0; i < as->wlitset.size(); i++){
		Aggr_watches[var(as->wlitset[i].lit)].push(AggrWatch(ae, i, sign(as->wlitset[i].lit) ? NEG : POS));
	}

	/*FIXME
	defType[var(c)] = AGGR;
	if (ecnf_mode.def){
		defdVars.push(var(c));
	}*/
}

/**
 * @PRE: literal p can be derived to be true because of the given aggregate reason
 *
 * it is then checked whether there is a conflict (construct conflict and add learned clause),
 * whether it can be propagated to the solver or whether it was already true.
 */
Clause* AggSolver::aggrEnqueue(Lit p, AggrReason* ar) {
	if (verbosity >= 2) {
		reportf("%seriving ", value(p)==l_True ? "Again d" : "D");
		printLit(p);
		reportf(" because of the aggregate expression ");
		printAggrExpr(*ar->expr, *ar->expr->set);
	}

	if (value(p) == l_False) {
		if (verbosity >= 2){
			reportf("Conflict.\n");
		}
		AggrReason* old_ar = aggr_reason[var(p)];
		aggr_reason[var(p)] = ar;
		Clause* confl = getExplanation(p);
		solver->addLearnedClause(confl);
		aggr_reason[var(p)] = old_ar;
		return confl;
	} else if (value(p) == l_Undef) {
		aggr_reason[var(p)] = ar;
		solver->setTrue(p);
	} else
		delete ar;
	return NULL;
}

Clause* AggSolver::Aggr_propagate(Lit p) { // TODO: do something about double work? E.g. first propagation head->some body literal, then backward again...
	Clause* confl = NULL;

	assert(!countedlit[toInt(p)]);
	countedlit[toInt(p)]=true;

	vec<AggrWatch>& ws = Aggr_watches[var(p)];
	if (verbosity >= 2 && ws.size() > 0){
		reportf("Aggr_propagate(%s%d).\n",sign(p)?"-":"",var(p)+1);
	}
	for (int i = 0; confl == NULL && i < ws.size(); i++) {
		Agg& ae = *ws[i].expr;
		Occurrence tp = relativeOccurrence(ws[i].type, p);
		ae.stack.push(PropagationInfo(p, ae.set->wlitset[ws[i].index].weight,tp));
		if (tp == HEAD) // The head literal has been propagated
			confl = ae.propagate(value(ae.head)==l_True);
		else { // It's a set literal.
			lbool result = ae.updateAndCheckPropagate(ae.set->wlitset[ws[i].index], tp==POS);
			if(result==l_True){
				confl = aggrEnqueue(ae.head, new AggrReason(&ae, HEAD));
			}else if(result==l_False){
				confl = aggrEnqueue(~ae.head, new AggrReason(&ae, HEAD));
			}else if(value(ae.head)!=l_Undef){
				confl = ae.propagate(value(ae.head)==l_True);
			}
		}
	}// TODO SUM / PROD propagations can be made more efficient using ordering of literals!!

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
	/*vec<Lit> lits;
	lits.push(p);

	AggrReason& ar = *aggr_reason[var(p)];
	int i = 0;
	for (; i < Aggr_watches[var(p)].size() && (Aggr_watches[var(p)])[i].set!= ar.set; ++i){
		;
	}
	assert(i<Aggr_watches[var(p)].size());
	int p_idx = (Aggr_watches[var(p)])[i].index;
	AggrType tp = ar.set->type;
	if (tp == SUM || tp == PROD) {
		int cmax = ar.set->cmax;
		int min_needed = tp == SUM ? 0 : 1;
		int max_needed = cmax;
		if (ar.type == HEAD) {
			// [mn >= i && mx =< j  ==>  c]  OR  [mn > j  || mx < i  ==>  ~c]
			if (ar.expr->c == p) {
				min_needed = ar.expr->min;
				max_needed = ar.expr->max;
			} else {
				assert(ar.expr->c==~p);
				if (ar.set->min > ar.expr->max)
					min_needed = ar.expr->max + 1;
				else
					max_needed = ar.expr->min - 1;
			}
		} else if (ar.type == POS) {
			// c is true && mx = i  OR  c is false && mn >= i && mx = j+1
			if (value(ar.expr->c) == l_True) {
				lits.push(~ar.expr->c);
				max_needed = ar.expr->min + ar.set->set[p_idx].weight - 1;
			} else {
				assert(value(ar.expr->c)==l_False);
				lits.push(ar.expr->c);
				min_needed = ar.expr->min;
				max_needed = ar.expr->max + ar.set->set[p_idx].weight;
			}
		} else {
			assert(ar.type==NEG);
			// c is true && mn = j  OR  c is false && mx =< j && mn = i-1
			if (value(ar.expr->c) == l_True) {
				lits.push(~ar.expr->c);
				min_needed = ar.expr->max - ar.set->set[p_idx].weight + 1;
			} else {
				assert(value(ar.expr->c)==l_False);
				lits.push(ar.expr->c);
				min_needed = ar.expr->min - ar.set->set[p_idx].weight;
				max_needed = ar.expr->max;
			}
		}

//		 We now walk over the stack and add literals that are relevant to the
//		 reason clause, until it is big enough. When that is depends on the type
//		 of propagation that was done to derive p.
//
		Lit q;
		char t;
		for (int i = 0; min_needed + (cmax - max_needed)
				> (ar.set->type == SUM ? 0 : 1); i++) {
			q = ar.set->stack[i].lit;
			assert(q!=p); // We should have assembled a reason clause before encountering this.
			t = ar.set->stack[i].type;

			// if (t==0) then q is irrelevant to this derivation.
			if (t == 1 && min_needed > (ar.set->type == SUM ? 0 : 1)) {
				lits.push(~q);
				if (ar.set->type == SUM)
					min_needed -= ar.set->stack[i].weight;
				else
					//PROD
					min_needed = min_needed / ar.set->stack[i].weight
							+ (min_needed % ar.set->stack[i].weight == 0 ? 0
									: 1);
			} else if (t == 2 && max_needed < cmax) {
				lits.push(~q);
				if (ar.set->type == SUM)
					max_needed += ar.set->stack[i].weight;
				else
					//PROD
					max_needed *= ar.set->stack[i].weight;
			}
		}
	} else { // tp == MIN or tp == MAX
		if (ar.type == HEAD) {
			if (ar.expr->c == p) {
				// NB: we're not using the stack now; assert that each of the used literals is on it, before p.
				if (tp == MIN) {
					for (int i = 0; i < ar.set->min && ar.set->set[i].weight
							< ar.expr->min; ++i)
						lits.push(ar.set->set[i].lit);
					assert(ar.set->max<ar.set->set.size() && ar.set->set[ar.set->max].weight >= ar.expr->min && ar.set->set[ar.set->max].weight <= ar.expr->max);
					lits.push(~ar.set->set[ar.set->max].lit);
				} else { // tp==MAX
					for (int i = ar.set->set.size() - 1; i > ar.set->max
							&& ar.set->set[i].weight > ar.expr->max; --i)
						lits.push(ar.set->set[i].lit);
					assert(ar.set->min>=0 && ar.set->set[ar.set->min].weight >= ar.expr->min && ar.set->set[ar.set->min].weight <= ar.expr->max);
					lits.push(~ar.set->set[ar.set->min].lit);
				}
			} else {
				assert(ar.expr->c==~p);
				// either the real MIN/MAX is too small, or too big.
				if (tp == MIN) {
					if (ar.set->max < ar.set->set.size()
							&& ar.set->set[ar.set->max].weight < ar.expr->min) {
						reportf("First option; ar.set->max=%d; its weight=%d; ar.expr->min=%d.\n",ar.set->max,ar.set->set[ar.set->max].weight,ar.expr->min);
						lits.push(~ar.set->stack[ar.set->max].lit);
					} else {
						assert(ar.set->max == ar.set->set.size() || ar.set->set[ar.set->min].weight>ar.expr->max); // NOTE: this does not assert that all these literals are on stack before p.
						reportf("Second option; ar.expr->max=%d.\n",ar.expr->max);
						for (int i = 0; i < ar.set->set.size()
								&& ar.set->set[i].weight <= ar.expr->max; ++i)
							lits.push(ar.set->set[i].lit);
					}
				} else { // tp==MAX
					if (ar.set->min >= 0 && ar.set->set[ar.set->min].weight
							> ar.expr->max)
						lits.push(~ar.set->stack[ar.set->min].lit);
					else {
						assert(ar.set->min < 0 || ar.set->set[ar.set->max].weight<ar.expr->min); // NOTE: this does not assert that all these literals are on stack before p.
						for (int i = ar.set->set.size() - 1; i >= 0
								&& ar.set->set[i].weight >= ar.expr->min; ++i)
							lits.push(ar.set->set[i].lit);
					}
				}
			}
		} else if (ar.type == POS) {
			assert(false); // This type of propagation should not occur as long as the (@&) TODO's haven't been implemented.
//			           if (value(ar.expr->c)==l_True) {
//			 lits.push(~ar.expr->c);
//			 } else { assert(value(ar.expr->c)==l_False);
//			 lits.push(ar.expr->c);
//			 }
//
		} else {
			assert(ar.type==NEG);
			if (tp == MIN) {
				if (value(ar.expr->c) == l_True) // assert that p's weight is < ar.expr->min
					lits.push(~ar.expr->c);
				else {
					assert(value(ar.expr->c)==l_False);
					lits.push(ar.expr->c);
					for (int i = 0; i < ar.set->set.size()
							&& ar.set->set[i].weight < ar.expr->min; ++i)
						lits.push(ar.set->set[i].lit); // assert that these literals are on the stack, before p.
				}
			} else { // tp==MAX
				if (value(ar.expr->c) == l_True) // assert that p's weight is > ar.expr->max
					lits.push(~ar.expr->c);
				else {
					assert(value(ar.expr->c)==l_False);
					lits.push(ar.expr->c);
					for (int i = ar.set->set.size() - 1; i >= 0
							&& ar.set->set[i].weight > ar.expr->max; ++i)
						lits.push(ar.set->set[i].lit); // assert that these literals are on the stack, before p.
				}
			}
		}
	}

	Clause* c = Clause_new(lits, true);
	if (verbosity >= 2) {
		reportf("Implicit reason clause for ");
		printLit(p);
		reportf(" : ");
		printClause(*c);
		reportf("\n");
	}

	return c;*/
	return NULL;
}

/**
 * SUM: substract the weight if positive, add the weight if negative
 * PROD: divide by weight if positive, multiply by weight if negative
 * MIN:	if equal to current max, find new max if positive,
 * 		if equal to current min, find new min if negative
 * MAX: reverse
 */
void AggSolver::backtrackOnePropagation(Agg& ae, Occurrence tp, int index){
	if (tp == HEAD){ //propagation didn't affect min/max
		return;
	}

	PropagationInfo pi = ae.stack.last();
	ae.stack.pop();
	assert(tp == pi.type);
	bool wasinset = tp == POS; 	//pos means that a literal that was already certainly in the set is now only possibly in the set
								//neg means that instead of certainly out, it now might be
	ae.backtrack(ae.set->wlitset[index], wasinset);
}

/**
 * Correct the min and max values of the aggregates in which l was propagated
 */
void AggSolver::doBacktrack(Lit l){
	//TODO review
	if (aggr_reason[var(l)] != NULL) {
		delete aggr_reason[var(l)];
		aggr_reason[var(l)] = NULL;
	}
	//TODO end review

	if(countedlit[toInt(l)]){
		countedlit[toInt(l)] = false;

		vec<AggrWatch>& vcw = Aggr_watches[var(l)];
		for(int i=0; i<vcw.size(); i++){
			Agg& ae = *vcw[i].expr;
			if(ae.stack.size()!=0 && var(ae.stack.last().wlit.lit)==var(l)){
				backtrackOnePropagation(ae, vcw[i].type, vcw[i].index);
			}
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

//=================================================================================================
// Debug + etc:

inline void AggSolver::printLit(Lit l) {
	reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}

template<class C>
inline void AggSolver::printClause(const C& c) {
	for (int i = 0; i < c.size(); i++) {
		printLit(c[i]);
		fprintf(stderr, " ");
	}
}


inline void AggSolver::printAggrSet(const AggrSet& as){
    for (int i=0; i<as.wlitset.size(); ++i) {
        reportf(" "); printLit(as.wlitset[i].lit); reportf("(%d)",as.wlitset[i].weight);
    }
}

inline void AggSolver::printAggrExpr(const Agg& ae, const AggrSet& as){
	//TODO repair aggregate printing
	reportf("Repair aggregate printing");
    /*printLit(ae.c); reportf(" <- %d <= %s{",ae.min, ae.type==SUM ? "sum" : (ae.type==PROD ? "prod" : (ae.type==MIN ? "min" : "max")));
    printAggrSet(as);
    reportf(" } <= %d. Known values: min=%d, max=%d\n",ae.max,as.min,as.max);*/
}
