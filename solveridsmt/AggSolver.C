#include "AggSolver.h"

AggSolver::AggSolver() :
	init(true), empty(false) {
}

AggSolver::~AggSolver() {
}

inline lbool AggSolver::value(Var x) const {
	return solver->value(x);
}
inline lbool AggSolver::value(Lit p) const {
	return solver->value(p);
}
inline int AggSolver::nVars() const {
	return solver->nVars();
}

void AggSolver::notifyVarAdded(){
	Aggr_watches.push();
	aggr_reason.push();
}

void AggSolver::finishECNF_DataStructures() {
	init = false;

	if (verbosity >= 1)
		reportf("| Number of aggregate exprs.: %4d",aggr_exprs.size());
	if (aggr_exprs.size() == 0) {
		solver->setAggSolver(NULL);
		if (verbosity >= 1) {
			reportf("                                            |\n");
			reportf("|    (there will be no aggregate propagations)                                |\n");
		}
		return;
	} else {
		int total_nb_set_lits = 0;
		for (int i = 0; i < aggr_sets.size(); i += NB_AGGR_TYPES)
			total_nb_set_lits += aggr_sets[i]->set.size();
		if (verbosity >= 1)
			reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",aggr_sets.size()/NB_AGGR_TYPES,(double)total_nb_set_lits/(double)(aggr_sets.size()/NB_AGGR_TYPES));
		// Now do the initial propagations based on set literals that already have a truth value.
		Clause * confl = NULL;
		for (int i = 0; i < solver->qhead && confl == NULL; ++i) // from qhead onwards will still be propagated by simplify().
			confl = Aggr_propagate(solver->trail[i]);
		if (confl != NULL) {
			throw theoryUNSAT;
		}
	}
}

Clause* AggSolver::aggrEnqueue(Lit p, AggrReason* ar) {
	if (verbosity >= 2) {
		reportf("%seriving ", value(p)==l_True ? "Again d" : "D");
		printLit(p);
		reportf(" because of the aggregate expression ");
		printAggrExpr(*ar->expr, *ar->set);
	}

	if (value(p) == l_False) {
		if (verbosity >= 2)
			reportf("Conflict.\n");
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

void AggSolver::addSet(int set_id, vec<Lit>& lits, vec<int>& weights) {
	if (lits.size() == 0) {
		reportf("Error: Set nr. %d is empty,\n",set_id);
		exit(3);
	}
	assert(lits.size()==weights.size());
	// Find out if lits contains any doubles.
	vec<Lit> ps(lits.size());
	for (int i = 0; i < lits.size(); i++){
		ps[i] = lits[i];
	}

	sort(ps);
	Lit previous = lit_Undef;
	for (int i = 0; i < ps.size(); i++){
		if (ps[i] == previous || ps[i] == ~previous){
			//TODO correct the code such that at least an atom and its negation can be used in the same expression
			reportf("ERROR! (W)Set %d contains the same literal ", set_id);
			printLit(previous);	reportf(" twice. Please use a placeholder.\n");
			exit(3);
		} else{
			previous = ps[i];
		}
	}
	// For each set_id we add NB_AGGR_TYPES sets.
	while (set_id * NB_AGGR_TYPES > aggr_sets.size())
		aggr_sets.push(new AggrSet()); // NOTE: each of these has type "SUM"!
	// But we only initialize the default one.
	AggrSet &as = *aggr_sets[(set_id - 1) * NB_AGGR_TYPES + SUM];
	if (as.set.size() > 0) {
		reportf("Error: Set nr. %d is defined more then once.\n",set_id), exit(
				3);
	}
	for (int i = 0; i < lits.size(); i++) {
		if (weights[i] < 0) {
			reportf("Error: Set nr. %d contains a negative weight, %d.\n",set_id,weights[i]), exit(
					3);
		}
		as.set.push(AggrSet::WLit(lits[i], weights[i]));
		as.max += weights[i];
	}
	qsort(as.set, as.set.size(), sizeof(AggrSet::WLit), compare_WLits);
	as.cmax = as.max;
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

/*
 Adds an aggregate expression.
 Revisions of these expressions, in case of non-standard weights, will be
 done at a later time. These revisions introduce new atoms; something which
 can be done only after parsing.

 NOTE ???: do not set "ecnf_mode.aggr=true" yet!! Then it will already
 propagate, but in that case the constraint that each derived literal is
 added only once to the queue would be required (otherwise "trues" and
 "falses" get too many counts.)
 */
void AggSolver::addAggrExpr(int defn, int set_id, int min, int max, AggrType type) {
	if (set_id * NB_AGGR_TYPES > aggr_sets.size()) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",set_id), exit(
				3);
	}
	if (min < 0 || min > max) {
		reportf("Error: aggregate expression with minimum %d and maximum %d is not valid.\n",min,max), exit(
				3);
	}

	Lit c = Lit(defn, false);

	//TODObroes add if really usefull varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.
	/*FIXME
	defType[var(c)] = AGGR;
	if (ecnf_mode.def){
		defdVars.push(var(c));
	}*/
	AggrExpr* ae = new AggrExpr(min, max, c);
	aggr_exprs.push(ae);
	AggrSet* as = aggr_sets[(set_id - 1) * NB_AGGR_TYPES + type];
	as->exprs.push(ae);
	if (as->type == SUM && type != SUM) {
		// It's the first aggregate expression of type 'type' for this set. Initialize the set.
		as->type = type;
		AggrSet* sum_as = aggr_sets[(set_id - 1) * NB_AGGR_TYPES + SUM]; // We'll copy from this set, which has been initialized already.
		for (int i = 0; i < sum_as->set.size(); i++)
			as->set.push(sum_as->set[i]);
		switch (as->type) {
		// If type=SUM or PROD: min/max  attainable with current truth values. If type=MIN: index of first non-false / first true literal (can go out of range!); if type=MAX: index of last true / last non-false literal (can go out of range!).
		case PROD:
			as->min = 1;
			as->max = 1;
			for (int i = 0; i < sum_as->set.size(); i++)
				as->max *= sum_as->set[i].weight;
			as->cmax = as->max;
			if (as->cmax == 0)
				reportf("ERROR! Weight zero in a PROD expression.\n"), exit(3);
			break;
		case MIN:
			as->min = 0; // [,)
			as->max = as->set.size(); // [,)
			break;
		case MAX:
			as->min = -1; // (,]
			as->max = as->set.size() - 1; // (,]
			break;
		default:
			assert(false);
			break;
		}
	}

	Aggr_watches[var(c)].push(AggrWatch(as, ae, -1, DEFN));

	bool already_occurs = false; // Making sure that for a set with several expressions, watches from the set literals are added only once.
	vec<AggrWatch>& vcw = Aggr_watches[var(as->set[0].lit)]; // Note: set is not empty.
	for (int i = 0; !already_occurs && i < vcw.size(); i++)
		if (vcw[i].set == as)
			already_occurs = true;
	for (int i = 0; !already_occurs && i < as->set.size(); i++)
		Aggr_watches[var(as->set[i].lit)].push(AggrWatch(as, NULL, i, sign(
				as->set[i].lit) ? NEG : POS));
}

Clause* AggSolver::Aggr_propagate(Lit p) { // TODO: do something about double work? E.g. first propagation head->some body literal, then backward again...
	Clause* confl = NULL;

	vec<AggrWatch>& ws = Aggr_watches[var(p)];
	if (verbosity >= 2 && ws.size() > 0)
		reportf("Aggr_propagate(%s%d).\n",sign(p)?"-":"",var(p)+1);
	for (int i = 0; confl == NULL && i < ws.size(); i++) {
		AggrSet& as = *ws[i].set;
		Occurrence tp = relativeOccurrence(ws[i].type, p);
		as.stack.push(AggrSet::PropagationInfo(p, as.set[ws[i].index].weight,
				tp));
		if (tp == DEFN) // It's a defining literal.
			confl = Aggr_propagate(as, *ws[i].expr);
		else { // It's a set literal.
			// First update the set's "min" and "max" values.
			bool trues = tp == POS;
			switch (as.type) {
			case SUM:
				if (trues)
					as.min += as.set[ws[i].index].weight;
				else
					as.max -= as.set[ws[i].index].weight;
				break;
			case PROD:
				// NOTE: this assumes weights are different from zero!
				if (trues)
					as.min *= as.set[ws[i].index].weight;
				else {
					assert(as.max % as.set[ws[i].index].weight==0);
					as.max = as.max / as.set[ws[i].index].weight;
				}
				break;
			case MIN:
				if (trues) {
					if (ws[i].index < as.max)
						as.max = ws[i].index;
				} else {/*if (ws[i].index==as.min)*/
					while (as.min < as.set.size() && value(as.set[as.min].lit)
							== l_False)
						++as.min;
				}
				break;
			case MAX:
				if (trues) {
					if (ws[i].index > as.min)
						as.min = ws[i].index;
				} else {/*if (ws[i].index==as.max)*/
					while (as.max >= 0 && value(as.set[as.max].lit) == l_False)
						--as.max;
				}
				break;
			default:
				assert(false);
				break;
			}
			int min = as.min;
			int max = as.max;

			if (as.type == MIN) {
				if (as.min < as.set.size())
					min = as.set[as.min].weight;
				else
					min = 2147483647;
				if (as.max < as.set.size())
					max = as.set[as.max].weight;
				else
					max = 2147483647;
			} else if (as.type == MAX) {
				if (as.min >= 0)
					min = as.set[as.min].weight;
				else
					min = -1;
				if (as.max >= 0)
					max = as.set[as.max].weight;
				else
					max = -1;
			}
			// Now try to propagate.
			for (int e = 0; confl == NULL && e < as.exprs.size(); e++) {
				AggrExpr& ae = *as.exprs[e];
				if (min >= ae.min && max <= ae.max)
					confl = aggrEnqueue(ae.c, new AggrReason(&ae, &as, DEFN));
				else if (min > ae.max)
					confl = aggrEnqueue(~ae.c, new AggrReason(&ae, &as, DEFN));
				else if (max < ae.min)
					confl = aggrEnqueue(~ae.c, new AggrReason(&ae, &as, DEFN));
				else
					confl = Aggr_propagate(as, ae);
			}
		}
	}

	return confl;
}

Clause* AggSolver::Aggr_propagate(AggrSet& as, AggrExpr& ae) {
	Clause* confl = NULL;
	switch (as.type) {
	// TODO SUM / PROD propagations can be made more efficient using ordering of literals!!
	case SUM:
		if (value(ae.c) == l_True) {
			for (int u = 0; u < as.set.size(); u++) {
				if (value(as.set[u].lit) == l_Undef) {// no conflict possible
					if (as.min + as.set[u].weight > ae.max)
						aggrEnqueue(~as.set[u].lit, new AggrReason(&ae, &as,
								NEG));
					else if (as.max - as.set[u].weight < ae.min)
						aggrEnqueue(as.set[u].lit,
								new AggrReason(&ae, &as, POS));
				}
			}
		} else if (value(ae.c) == l_False) {
			if (as.min >= ae.min || as.max <= ae.max) {// no conflicts possible
				int minw = 2147483647;
				for (int u = 0; u < as.set.size(); u++)
					if (value(as.set[u].lit) == l_Undef && as.set[u].weight
							< minw)
						minw = as.set[u].weight;
				bool maketrue = minw != 2147483647 && as.min >= ae.min
						&& as.max - minw <= ae.max;
				bool makefalse = minw != 2147483647 && as.max <= ae.max
						&& as.min + minw >= ae.min;
				if (maketrue)
					for (int u = 0; u < as.set.size(); u++)
						if (value(as.set[u].lit) == l_Undef)
							aggrEnqueue(as.set[u].lit, new AggrReason(&ae, &as,
									POS));
				if (makefalse)
					for (int u = 0; u < as.set.size(); u++)
						if (value(as.set[u].lit) == l_Undef)
							aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,
									&as, NEG));
			}
		}
		break;
	case PROD: // cfr. SUM, but * and / instead of + and -.
		if (value(ae.c) == l_True) {
			for (int u = 0; u < as.set.size(); u++) {
				if (value(as.set[u].lit) == l_Undef) {
					if (as.min * as.set[u].weight > ae.max)
						aggrEnqueue(~as.set[u].lit, new AggrReason(&ae, &as,
								NEG));
					else if (as.max / as.set[u].weight < ae.min)
						aggrEnqueue(as.set[u].lit,
								new AggrReason(&ae, &as, POS));
				}
			}
		} else if (value(ae.c) == l_False) {
			if (as.min >= ae.min || as.max <= ae.max) {
				int minw = 2147483647;
				for (int u = 0; u < as.set.size(); u++)
					if (value(as.set[u].lit) == l_Undef && as.set[u].weight
							< minw)
						minw = as.set[u].weight;
				bool maketrue = minw != 2147483647 && as.min >= ae.min
						&& as.max / minw <= ae.max;
				bool makefalse = minw != 2147483647 && as.max <= ae.max
						&& as.min * minw >= ae.min;
				if (maketrue)
					for (int u = 0; u < as.set.size(); u++)
						if (value(as.set[u].lit) == l_Undef)
							aggrEnqueue(as.set[u].lit, new AggrReason(&ae, &as,
									POS));
				if (makefalse)
					for (int u = 0; u < as.set.size(); u++)
						if (value(as.set[u].lit) == l_Undef)
							aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,
									&as, NEG));
			}
		}
		break;
	case MIN:
		if (value(ae.c) == l_True) {
			for (int u = as.min; confl == NULL && u < as.set.size()
					&& as.set[u].weight < ae.min; ++u)
				confl = aggrEnqueue(~as.set[u].lit, new AggrReason(&ae, &as,
						NEG));
		} else if (value(ae.c) == l_False) {
			if (as.min < as.set.size() && as.set[as.min].weight >= ae.min)
				for (int u = as.min; confl == NULL && u < as.set.size()
						&& as.set[u].weight <= ae.max; ++u)
					confl = aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,
							&as, NEG));
		}
		break;
	case MAX:
		if (value(ae.c) == l_True) {
			for (int u = as.max; confl == NULL && u >= 0 && as.set[u].weight
					> ae.max; --u)
				confl = aggrEnqueue(~as.set[u].lit, new AggrReason(&ae, &as,
						NEG));
		} else if (value(ae.c) == l_False) {
			if (as.max >= 0 && as.set[as.max].weight <= ae.max)
				for (int u = as.max; confl == NULL && u >= 0
						&& as.set[u].weight >= ae.min; --u)
					confl = aggrEnqueue(~as.set[u].lit, new AggrReason(&ae,
							&as, NEG));
		}
		break;
	default:
		assert(false);
		break;
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
 |    Note that this clause is not attached, bumped, or any of the likes. Delete it immediately
 |    after use, to avoid memory leaks.
 |________________________________________________________________________________________________@*/
Clause* AggSolver::getExplanation(Lit p) {
	vec<Lit> lits;
	lits.push(p);

	AggrReason& ar = *aggr_reason[var(p)];
	int i = 0;
	for (; i < Aggr_watches[var(p)].size() && (Aggr_watches[var(p)])[i].set
			!= ar.set; ++i)
		;
	assert(i<Aggr_watches[var(p)].size());
	int p_idx = (Aggr_watches[var(p)])[i].index;
	AggrType tp = ar.set->type;
	if (tp == SUM || tp == PROD) {
		int cmax = ar.set->cmax;
		int min_needed = tp == SUM ? 0 : 1;
		int max_needed = cmax;
		if (ar.type == DEFN) {
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

		/* We now walk over the stack and add literals that are relevant to the
		 reason clause, until it is big enough. When that is depends on the type
		 of propagation that was done to derive p.
		 */
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
					/*PROD*/
					min_needed = min_needed / ar.set->stack[i].weight
							+ (min_needed % ar.set->stack[i].weight == 0 ? 0
									: 1);
			} else if (t == 2 && max_needed < cmax) {
				lits.push(~q);
				if (ar.set->type == SUM)
					max_needed += ar.set->stack[i].weight;
				else
					/*PROD*/
					max_needed *= ar.set->stack[i].weight;
			}
		}
	} else { // tp == MIN or tp == MAX
		if (ar.type == DEFN) {
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
			/*            if (value(ar.expr->c)==l_True) {
			 lits.push(~ar.expr->c);
			 } else { assert(value(ar.expr->c)==l_False);
			 lits.push(ar.expr->c);
			 }
			 */
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

	return c;
}

void AggSolver::doBacktrack(Lit l){
	// Fix the Aggregate min and max values.
	if (aggr_reason[var(l)] != NULL) {
		delete aggr_reason[var(l)];
		aggr_reason[var(l)] = NULL;
	}
	vec<AggrWatch>& vcw = Aggr_watches[var(l)];
	for (int i = 0; i < vcw.size(); i++) {
		if (vcw[i].set->stack.size() == 0 || var(l) != var(
				vcw[i].set->stack.last().lit)) // l hadn't yet propagated.
			continue;
		AggrSet::PropagationInfo pi = vcw[i].set->stack.last();
		vcw[i].set->stack.pop();
		Occurrence tp = relativeOccurrence(vcw[i].type, l);
		assert(tp == pi.type);
		if (tp == DEFN) // These propagations don't affect 'min' and 'max'.
			continue;
		bool trues = tp == POS;
		switch (vcw[i].set->type) {
		case SUM:
			if (trues)
				vcw[i].set->min -= vcw[i].set->set[vcw[i].index].weight;
			else
				vcw[i].set->max += vcw[i].set->set[vcw[i].index].weight;
			break;
		case PROD:
			if (trues)
				vcw[i].set->min = vcw[i].set->min
						/ vcw[i].set->set[vcw[i].index].weight;
			else
				vcw[i].set->max *= vcw[i].set->set[vcw[i].index].weight;
			break;
		case MIN:
			if (trues)
				while (vcw[i].set->max < vcw[i].set->set.size()
						&& value(vcw[i].set->set[vcw[i].set->max].lit)
								!= l_True)
					vcw[i].set->max++;
			else if (vcw[i].set->set[pi.weight].weight
					<= vcw[i].set->set[vcw[i].set->min].weight) // TODO PropagationInfo should have "index" too!
				while (vcw[i].set->min >= 0
						&& vcw[i].set->set[vcw[i].set->min].lit
								!= ~pi.lit)
					vcw[i].set->min--;

			break;
		case MAX:
			if (trues)
				while (vcw[i].set->min >= 0 && value(vcw[i].set->set[vcw[i].set->min].lit) != l_True)
					vcw[i].set->min--;
			else if (vcw[i].set->set[pi.weight].weight
					>= vcw[i].set->set[vcw[i].set->max].weight)
				while (vcw[i].set->max < vcw[i].set->set.size()
						&& vcw[i].set->set[vcw[i].set->max].lit
								!= ~pi.lit)
					vcw[i].set->max++;
			break;
		default:
			assert(false);
			break;
		}
	}
}

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
    for (int i=0; i<as.set.size(); ++i) {
        reportf(" "); printLit(as.set[i].lit); reportf("(%d)",as.set[i].weight);
    }
}

inline void AggSolver::printAggrExpr(const AggrExpr& ae, const AggrSet& as){
    printLit(ae.c); reportf(" <- %d <= %s{",ae.min, as.type==SUM ? "sum" : (as.type==PROD ? "prod" : (as.type==MIN ? "min" : "max")));
    printAggrSet(as);
    reportf(" } <= %d. Known values: min=%d, max=%d\n",ae.max,as.min,as.max);
}
