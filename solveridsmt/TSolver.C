#include "TSolver.h"

#include "Sort.h"
#include "Map.h"
#include <cmath>

TSolver::TSolver():
	defn_strategy(always),
	defn_search(include_cs),
	ufs_strategy(breadth_first),
	prev_conflicts(-1), /*first time test (prev_conflicts==conflicts) should fail*/
	cycle_sources(0), justifiable_cycle_sources(0),
	cycles(0),
	cycle_sizes(0),
	justify_conflicts(0), // ecnf_mode.def
	nb_times_findCS(0), justify_calls(0), cs_removed_in_justify(0),
	succesful_justify_calls(0), extdisj_sizes(0),
	total_marked_size(0)
	//  , fw_propagation_attempts(0), fw_propagations(0)
	,
	adaption_total(0),	adaption_current(0)
{
}

inline lbool    TSolver::value(Var x) const   { return solver->value(x); /* toLbool(assigns[x]); */}
inline lbool    TSolver::value(Lit p) const   { return solver->value(p); /*toLbool(assigns[var(p)]) ^ sign(p);*/ }
inline int      TSolver::nVars()      const   { return solver->nVars(); /*assigns.size();*/ }

TSolver::~TSolver() {
}

void TSolver::backtrack ( Lit l){
	if (!ecnf_mode.init && ecnf_mode.aggr) {
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
}

//@pre: conflicts are empty
bool TSolver::simplify(){
	// Note that ecnf_mode.init is still true, if this is the first time running simplify!
	ecnf_mode.init = false;
	bool old_ecnf_def = ecnf_mode.def;
	ecnf_mode.def = false;
	ecnf_mode.def = old_ecnf_def;

	// Initialization procedure to ensure correctness of subsequent indirectPropagate() calls.
	// This has to be done before the first choice.
	if (ecnf_mode.def) {
		// NOTE: we're doing a stable model initialization here. No need for a loop.
		cf_justification_disj.clear();
		cf_justification_disj.growTo(nVars());
		sp_justification_disj.clear();
		sp_justification_disj.growTo(nVars());
		cf_justification_aggr.clear();
		cf_justification_aggr.growTo(2 * nVars());
		sp_justification_aggr.clear();
		sp_justification_aggr.growTo(2 * nVars());

		vec<int> nb_body_lits_to_justify; // Note: use as boolean for DISJ and AGGR, as int for CONJ.
		nb_body_lits_to_justify.growTo(nVars(), 0); // Unless there are big conjunctions, we could use 'seen' instead of 'nb_body_lits_to_justify'.

		// *** First : initialize nb_body_lits_to_justify, and the propagation queue propq.
		for (int i = 0; i < defdVars.size(); i++) {
			Var v = defdVars[i];
			if (value(v) == l_False)
				continue;
			switch (defType[v]) {
			case DISJ:
				nb_body_lits_to_justify[v] = 1;
				break;
			case CONJ:
				nb_body_lits_to_justify[v] = definition[v]->size() - 1;
				break;
			case AGGR:
				nb_body_lits_to_justify[v] = 1;
				break;
			default:
				break;
			}
		}

		// *** Next: initialize a queue of literals that are safe with regard to cycle-freeness. (i.e.: either are not in justification, or are justified in a cycle-free way.)
		Queue<Lit> propq;
		for (int i = 0; i < nVars(); ++i)
			if (value(i) != l_True)
				propq.insert(Lit(i, true)); // First all non-false negative literals.
		for (int i = 0; i < nVars(); ++i)
			if (defType[i] == NONDEF && value(i) != l_False)
				propq.insert(Lit(i, false)); // Then all non-false non-defined positive literals.

		// *** Next: propagate safeness to defined literals until fixpoint.
		// While we do this, we build the initial justification.
		while (propq.size() > 0) {
			Lit l = propq.peek();
			propq.pop();

			for (int i = 0; i < disj_occurs[toInt(l)].size(); ++i) { // Find disjunctions that may be made cycle-safe through l.
				Var v = (disj_occurs[toInt(l)])[i];
				if (defType[v] == NONDEF || value(v) == l_False)
					continue;
				assert(defType[v]==DISJ);
				if (nb_body_lits_to_justify[v] > 0) {
					nb_body_lits_to_justify[v] = 0;
					propq.insert(Lit(v, false));
					cf_justification_disj[v] = l;
					sp_justification_disj[v] = l;
				}
			}
			for (int i = 0; i < conj_occurs[toInt(l)].size(); ++i) { // Find conjunctions that may be made cycle-safe through l.
				Var v = (conj_occurs[toInt(l)])[i];
				if (defType[v] == NONDEF || value(v) == l_False)
					continue;
				assert(defType[v]==CONJ);
				--nb_body_lits_to_justify[v];
				if (nb_body_lits_to_justify[v] == 0)
					propq.insert(Lit(v, false));
			}
			if (ecnf_mode.aggr) { // TODO
				for (int i = 0; i < Aggr_watches[var(l)].size(); ++i) { // Find aggregate expressions that may be made cycle-safe through l.
					AggrWatch& aw = (Aggr_watches[var(l)])[i];
					if (aw.type == DEFN)
						continue;
					vec<AggrExpr*>& exprs = aw.set->exprs;
					for (int j = 0; j < exprs.size(); ++j) {
						Var v = var(exprs[j]->c);
						if (defType[v] == NONDEF || value(v) == l_False)
							continue;
						assert(defType[v]==AGGR);
						if (nb_body_lits_to_justify[v] > 0) {
							vec<Lit> jstf; // Only add it if complete (!nb_body_lits_to_justify[v]).
							vec<AggrSet::WLit>& lits = aw.set->set;
							switch (aw.set->type) {
							case SUM: {
								int min = 0;
								int max = aw.set->cmax;
								bool complete = false;
								for (int k = 0; !complete && k < lits.size(); ++k) {
									Lit ll = lits[k].lit;
									if (value(ll) != l_False) {
										if (sign(ll)
												|| nb_body_lits_to_justify[var(
														ll)] == 0) {
											jstf.push(ll);
											min += lits[k].weight;
											if (min >= exprs[j]->min && max
													<= exprs[j]->max)
												complete = true;
										}
									}
									if (value(ll) != l_True) {
										if (!sign(ll)
												|| nb_body_lits_to_justify[var(
														ll)] == 0) {
											jstf.push(~ll);
											max -= lits[k].weight;
											if (min >= exprs[j]->min && max
													<= exprs[j]->max)
												complete = true;
										}
									}
								}
								if (complete)
									nb_body_lits_to_justify[v] = 0;
								break;
							}
							case PROD: {
								int min = 1;
								int max = aw.set->cmax;
								bool complete = false;
								for (int k = 0; !complete && k < lits.size(); ++k) {
									Lit ll = lits[k].lit;
									if (value(ll) != l_False) {
										if (sign(ll)
												|| nb_body_lits_to_justify[var(
														ll)] == 0) {
											jstf.push(ll);
											min *= lits[k].weight;
											if (min >= exprs[j]->min && max
													<= exprs[j]->max)
												complete = true;
										}
									}
									if (value(ll) != l_True) {
										if (!sign(ll)
												|| nb_body_lits_to_justify[var(
														ll)] == 0) {
											jstf.push(~ll);
											max = max / lits[k].weight;
											if (min >= exprs[j]->min && max
													<= exprs[j]->max)
												complete = true;
										}
									}
								}
								if (complete)
									nb_body_lits_to_justify[v] = 0;
								break;
							}
							case MIN: {
								bool aux = true;
								int k = 0;
								for (; aux && lits[k].weight < exprs[j]->min; ++k) {
									Lit ll = lits[k].lit;
									if (!sign(ll)
											|| nb_body_lits_to_justify[var(ll)]
													== 0)
										jstf.push(~ll);
									else
										aux = false;
								}// NB: 'aux' switches meaning inbetween here...
								for (; aux && lits[k].weight <= exprs[j]->max; ++k) {
									Lit ll = lits[k].lit;
									if (value(ll) != l_False && (sign(ll)
											|| nb_body_lits_to_justify[var(ll)]
													== 0)) {
										jstf.push(ll);
										aux = false;
									}
								}
								if (!aux)
									nb_body_lits_to_justify[v] = 0;
								break;
							}
							case MAX: {
								bool aux = true;
								int k = lits.size() - 1;
								for (; aux && lits[k].weight > exprs[j]->max; --k) {
									Lit ll = lits[k].lit;
									if (!sign(ll)
											|| nb_body_lits_to_justify[var(ll)]
													== 0)
										jstf.push(~ll);
									else
										aux = false;
								}// NB: 'aux' switches meaning inbetween here...
								for (; aux && lits[k].weight >= exprs[j]->min; --k) {
									Lit ll = lits[k].lit;
									if (value(ll) != l_False
											&& (!sign(ll)
													|| !nb_body_lits_to_justify[var(
															ll)])) {
										jstf.push(ll);
										aux = false;
									}
								}
								if (!aux)
									nb_body_lits_to_justify[v] = 0;
								break;
							}
							}
							if (nb_body_lits_to_justify[v] == 0) {
								propq.insert(Lit(v, false));
								assert(sp_justification_aggr[v].size()==0);
								assert(cf_justification_aggr[v].size()==0);
								for (int j = 0; j < jstf.size(); ++j) {
									sp_justification_aggr[v].push(jstf[j]);
									cf_justification_aggr[v].push(jstf[j]);
								}
							}
						}
					}
				}
			}
		}

		// *** Finally, vars v that still have nb_body_lits_to_justify[v]>0 can never possibly become true: make them false.
		if (verbosity >= 2)
			reportf("Initialization of justification makes these atoms false: [");
		vec<Lit> empty;
		for (int i = 0; i < defdVars.size(); i++) {
			Var v = defdVars[i];
			if (nb_body_lits_to_justify[v] > 0) {
				if (verbosity >= 2)
					reportf(" %d",v+1);

				/*Lit p = Lit(v, true);
				if(value(v)==l_Undef){
					solver->setTrue(p);
				}else if(value(p)==l_False){
						return false;
				}*/

				Lit p = Lit(v,true);
				if (!(value(p) != l_Undef ? value(p) != l_False : (solver->setTrue(p, NULL), true)))
				  throw theoryUNSAT;

				defType[v] = NONDEF;
				--atoms_in_pos_loops;
			}
		}
		if (verbosity >= 2)
			reportf(" ]\n");

		if (atoms_in_pos_loops == 0)
			ecnf_mode.def = false;

		if (atoms_in_pos_loops == 0 && verbosity >= 1)
			reportf("| All recursive atoms falsified in initializations.                           |\n");
		//if (ecnf_mode.def && verbosity>=2) assert(isCycleFree()); // Only for debugging!!
	}

	if (verbosity >= 2 && (ecnf_mode.def || ecnf_mode.aggr))
		reportf("ECNF data structures initialized and theory simplified.\n");
	return true;
}

Clause* TSolver::propagate(Lit p, Clause* confl){
	if (ecnf_mode.init) {
		return confl;
	}

	// Aggr propagations.
	if (confl == NULL && ecnf_mode.aggr)
		return Aggr_propagate(p);

	// TODO: fast way of stopping the while loop if confl != NULL ?
	return confl;
}

//only call this when the whole queue has been propagated
Clause* TSolver::propagateDefinitions(Clause* confl){
	if (ecnf_mode.init) {
		return confl;
	}

	// Def propagations.
	if (confl == NULL && ecnf_mode.def){
		return indirectPropagate();
	}
	return confl;
}

void TSolver::notifyVarAdded(){
	seen.push(0);
	seen2.push(0);

	if (ecnf_mode.def) {
		defType.push(NONDEF);
		definition.push(NULL);
		disj_occurs.growTo(2 * nVars()); // May be tested on in findCycleSources().
		conj_occurs.growTo(2 * nVars()); // Probably not needed anyway...
	}
	if (ecnf_mode.aggr) {
		Aggr_watches.push();
		aggr_reason.push();
	}
}

// First literal in ps is head atom.
bool TSolver::addRule(bool conj, vec<Lit>& ps) {
	if (!ecnf_mode.def)
		reportf("ERROR! Attempt at adding rule, though ECNF specifiers did not contain \"def\".\n"), exit(3);
	assert(ps.size() > 0);
	assert(!sign(ps[0]));

	//rules with only one body atom have to be treated as conjunctive
	if(ps.size()==2 && !conj){
		conj=true;
	}

	if (conj){
		for (int i = 1; i < ps.size(); i++){
			ps[i] = ~ps[i];
		}
	}else{
		ps[0] = ~ps[0];
	}

	if (ps.size() == 1) {
		// Remark: disjunctive rule with empty body: head is false!
		if (value(ps[0]) == l_False){
			throw theoryUNSAT;
		}
		vec<Lit> v;
		v.push(ps[0]);
		solver->addClause(v);
	} else {
		//Rule* r = Rule_new(ps);
		Clause* c = Clause_new(ps, false);
		//add completion to SAT solver
		solver->addClause(c);
		Var v = var(ps[0]);
		defdVars.push(v);
		defType[v] = conj ? CONJ : DISJ;
		definition[v] = c;

		//add completion to SAT solver 2
		vec<Lit> binclause(2);
		binclause[0] = ~ps[0];
		for (int i = 1; i < ps.size(); i++) {
			binclause[1] = ~ps[i];
			c = Clause_new(binclause, false);
			solver->addClause(c);
		}
		//add completion to SAT solver (rule)
		//solver->addClause(ps);
	}

	return true;
}

//=================================================================================================
// SAT(ID) additional methods

// Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
void TSolver::finishECNF_DataStructures() {
	if (ecnf_mode.aggr) {
		if (verbosity >= 1)
			reportf("| Number of aggregate exprs.: %4d",aggr_exprs.size());
		if (aggr_exprs.size() == 0) {
			ecnf_mode.aggr = false;
			if (verbosity >= 1) {
				reportf("                                            |\n");
				reportf("|    (there will be no aggregate propagations)                                |\n");
			}
		} else {
			int total_nb_set_lits = 0;
			for (int i = 0; i < aggr_sets.size(); i += NB_AGGR_TYPES)
				total_nb_set_lits += aggr_sets[i]->set.size();
			if (verbosity >= 1)
				reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",aggr_sets.size()/NB_AGGR_TYPES,(double)total_nb_set_lits/(double)(aggr_sets.size()/NB_AGGR_TYPES));
			// Now do the initial propagations based on set literals that already have a truth value.
			// Note: this is based on the fact that until now ecnf_mode.init=false.
			Clause * confl = NULL;
			for (int i = 0; i < solver->qhead && confl == NULL; ++i) // from qhead onwards will still be propagated by simplify().
				confl = Aggr_propagate(solver->trail[i]);
			if (confl != NULL) {
				throw theoryUNSAT;
			}
		}
	}

	if (ecnf_mode.def) {
		if (verbosity >= 1)
			reportf("| Number of rules           : %6d                                          |\n",defdVars.size());

		// ****** Based on this, initialize "scc". ******
		scc.growTo(nVars(), 0);
		//for memory efficiency, the scc datastructure is used to keep the root of the nodes
		//in the end, the algorithm sets ALL of the nodes on the stack to the same root
		//so then the SCC is correct
		vec<int> & root = scc;
		vec<bool> incomp(nVars(), false);
		vec<int> stack;
		vec<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to a unique value (the counter).
		int counter = 1;

        for (int i=0; i<nVars(); i++){
        	if (defType[i]!=NONDEF && visited[i]==0){
        		visit(i,root,incomp,stack,visited,counter);
        	}
        }

		// Based on "scc", determine which atoms should actually be considered defined. Meanwhile initialize "disj_occurs" and "conj_occurs".
		// NOTE: because we've searched scc's in the *positive* dependency graph, rules like  P <- ~Q, Q <- ~P will be marked NONDEF here. Hence final well-foundedness check needs to check in defdVars.
		atoms_in_pos_loops = 0;
		disj_occurs.growTo(2 * nVars());
		conj_occurs.growTo(2 * nVars());
		Lit l;
		Lit jstf;
		for (int i = 0; i < defdVars.size(); ++i) {
			Var v = defdVars[i];
			bool isdefd = false;
			switch (defType[v]) {
			case DISJ: {
				Clause& dfn = *definition[v];
				//Rule& dfn = *definition[v];
				for (int j = 0; j < dfn.size(); ++j) {
					l = dfn[j];
					if (l != Lit(v, true))
						disj_occurs[toInt(l)].push(v);
					if (!sign(l) && scc[v] == scc[var(l)])
						isdefd = true;
				}
				break;
			}
			case CONJ: {
				Clause& dfn = *definition[v];
				//Rule& dfn = *definition[v];
				for (int j = 0; j < dfn.size(); ++j) {
					l = ~dfn[j];
					if (l != Lit(v, true))
						conj_occurs[toInt(l)].push(v);
					if (!sign(l) && scc[v] == scc[var(l)])
						isdefd = true;
				}
				break;
			}
			case AGGR: {
				assert(ecnf_mode.aggr);
				AggrWatch& aw = (Aggr_watches[v])[0];
				for (int j = 0; !isdefd && j < aw.set->set.size(); ++j)
					if (scc[v] == scc[var(aw.set->set[j].lit)]) // NOTE: disregard sign here: set literals can occur both pos and neg in justifications. This could possibly be made more precise for MIN and MAX...
						isdefd = true;
				break;
			}
			default:
				assert(false);
			}
			if (isdefd)
				atoms_in_pos_loops++;
			else
				defType[v] = NONDEF; // NOTE: no reason to set definition[v]=NULL.
		}
		if (verbosity >= 1)
			reportf("| Number of recursive atoms : %6d                                          |\n",(int)atoms_in_pos_loops);
		if (atoms_in_pos_loops == 0) {
			ecnf_mode.def = false;
			if (verbosity >= 1)
				reportf("|    (there will be no definitional propagations)                             |\n");
		}

		if (ecnf_mode.def) {
			isCS.growTo(nVars(), false);
			// used_conj.growTo(nVars()); WITH guards system.
		}
		// TODO verify whether there could still be propagations pending due to the fact that rules are not simplified while parsing.
	}
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the
 * POSITIVE dependency graph.
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * #post: the scc will be denoted by the variable in the scc which was visited first
 */
void TSolver::visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter) {
	assert(defType[i]!=NONDEF);
	assert(!incomp[i]);
	visited[i] = ++counter;
	root[i] = i;
	stack.push(i);

	switch (defType[i]) {
	case DISJ: {
		for (int j = 0; j < definition[i]->size(); ++j) {
			Lit l = (*definition[i])[j];
			int w = var(l);
			if (defType[w] != NONDEF && i != w && !sign(l)) {
				if (visited[w]==0){
					visit(w,root,incomp,stack,visited,counter);
				}
				if (!incomp[w] && visited[root[i]]>visited[root[w]]){
					root[i] = root[w];
				}
			}
		}
		break;
	}
	case CONJ: {
		for (int j = 0; j < definition[i]->size(); ++j) {
			Lit l = (*definition[i])[j];
			int w = var(l);
			//TODObroes een conjunctieve rule wordt ALTIJD uitgeschreven (completion) als head OR not bodyx OR not bodyx2 ...
			//dus een conjunctieve rule gaat altijd al zijn positieve defined kinderen volgen
			if (defType[w] != NONDEF && i != w && sign(l)) {
				if (visited[w]==0){
					visit(w,root,incomp,stack,visited,counter);
				}
				if (!incomp[w] && visited[root[i]]>visited[root[w]]){
					root[i] = root[w];
				}
			}
		}
		break;
	}
	case AGGR: {
		AggrWatch& aw = (Aggr_watches[i])[0];
		for (int j = 0; j < aw.set->set.size(); ++j) {
			Var w = var(aw.set->set[j].lit);
			if (defType[w] != NONDEF) {
				if (visited[w]==0){
					visit(w,root,incomp,stack,visited,counter);
				}
				if (!incomp[w] && visited[root[i]]>visited[root[w]]){
					root[i] = root[w];
				}
			}
		}
		break;
	}
	default:
		assert(false);
	}
	if (root[i] == i) {
		int w;
		do {
			w = stack.last();
			stack.pop();
			//these are the found sccs
			root[w] = i;
			incomp[w] = true;
		} while (w != i);
	}
}

/**
 * Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void TSolver::findCycleSources() {
	clearCycleSources();
	clear_changes();

	//ADDED LAST PART FOR CONSISTENCY
	if (prev_conflicts == solver->conflicts && defn_strategy == always && solver->decisionLevel()!=0) {
		/*for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
			Lit x = solver->getRecentAssignments(i);
			if(value(x)==l_True){
				x = ~x;
			}
			for(int j=0; j<disj_occurs[toInt(x)].size(); j++) {
				Var v = disj_occurs[toInt(x)][j];
				if(defType[v]==CONJ || defType[v]==DISJ || defType[v]==AGGR){
					addCycleSource(v);
				}
			}
		}*/

		//for (int i=solver->trail_lim.last(); i<solver->trail.size(); i++) {
		//	Lit l = solver->trail[i]; // l became true, ~l became false.
		for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
			Lit l = solver->getRecentAssignments(i);
			vec<Var>& ds = disj_occurs[toInt(~l)];
			for (int j = 0; j < ds.size(); j++) {
				Var v = ds[j];
				if (value(v) != l_False && cf_justification_disj[v] == ~l) // No support anymore; it has to change.
					findCycleSources(v);
			}
			if (ecnf_mode.aggr) {
				// Aggr_watches[v] is a list of sets in which v occurs (each AggrWatch says: which set, what type of occurrence).
				// If defType[v]==AGGR, (Aggr_watches[v])[0] has type==DEFN and expr->c==Lit(v,false).
				vec<AggrWatch>& as = Aggr_watches[var(l)];
				for (int j = 0; j < as.size(); j++) {
					AggrWatch& aw = as[j];
					if (aw.type != DEFN) { // ~l is possibly used in the defining atom's cf_justification.
						for (int e = 0; e < aw.set->exprs.size(); e++) {
							Lit defn = aw.set->exprs[e]->c;
							//Lit defn = aw.expr->c;
							if (value(defn) != l_False) {
								vec<Lit>& cf = cf_justification_aggr[var(defn)];
								int k = 0;
								for (; k < cf.size() && cf[k] != ~l; k++)
									;
								if (k < cf.size()) // ~l is indeed used in the cf_justification.
									findCycleSources(var(defn));
							}
						}
					}
				}
			}
		}
	} else {
		/*for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
			Lit x = solver->getRecentAssignments(i);
			if(value(x)==l_True){
				x = ~x;
			}
			for(int j=0; j<disj_occurs[toInt(x)].size(); j++) {
				Var v = disj_occurs[toInt(x)][j];
				if(defType[v]==CONJ || defType[v]==DISJ || defType[v]==AGGR){
					addCycleSource(v);
				}
			}
		}*/
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		prev_conflicts = solver->conflicts;
		for (int i = 0; i < defdVars.size(); i++) {
			Var v = defdVars[i];
			if (defType[v] == DISJ) {
				if (value(v) != l_False && value(cf_justification_disj[v]) == l_False)
					findCycleSources(v);
			} else if (defType[v] == AGGR) {
				if (value(v) == l_False)
					continue;
				vec<Lit>& cf = cf_justification_aggr[v];
				int k = 0;
				for (; k < cf.size() && value(cf[k]) != l_False; k++)
					;
				if (k < cf.size()) // There is a false literal in the cf_justification.
					findCycleSources(v);
			}
		}
	}
	nb_times_findCS++;
	cycle_sources += css.size();
	if (verbosity >= 2) {
		reportf("Indirect propagations. Verifying %d cycle sources:",css.size());
		for (int i = 0; i < css.size(); ++i)
			reportf(" %d",css[i]+1);
		reportf(".\n");
	}
}

// Precondition: V is of type DISJ or AGGR. It is non-false, and its cf_justification does not support it.
// Postcondition: sp_justification..[v] supports v. v is added a cycle source if necessary (i.e., if there might be a cycle through its sp_justification).
void TSolver::findCycleSources(Var v) {
	if (isCS[v])
		return;
	if (defType[v] == DISJ) {
		Clause& c = *definition[v];
		//Rule& c = *definition[v];
		//TODObroes IMPLICIETE INVARIANT HIER is dat minisat zijn clauses herordend, zodat de eerste of de tweede literal false zijn!!!
		Lit jstf = c[c[0] == Lit(v, true) ? 1 : 0]; // We will use this literal as the supporting literal.
		assert(value(jstf)!=l_False);
		change_jstfc_disj(v, jstf);
		if (!sign(jstf) && defType[var(jstf)] != NONDEF && scc[v] == scc[var(
				jstf)])
			addCycleSource(v);
	} else {
		assert(defType[v]==AGGR);
		bool becomes_cycle_source = false;

		AggrWatch& aw = (Aggr_watches[v])[0];
		vec<AggrSet::WLit>& lits = aw.set->set;
		vec<Lit> nj; // New sp_justification.
		if (aw.set->type == SUM || aw.set->type == PROD) { // Note: no need to test weights, because v is not false.
			for (int i = 0; i < lits.size(); ++i) { // Also note: here we make a huge simplification of possible justifications. It has the advantage of being uniquely defined, and the disadvantage of a higher chance of adding v as a cycle source.
				Lit k = lits[i].lit;
				if (value(k) == l_Undef) {
					nj.push(k);
					nj.push(~k);
					if (!becomes_cycle_source && defType[var(k)] != NONDEF
							&& scc[v] == scc[var(k)]) // first test: to avoid having to do other tests.
						becomes_cycle_source = true;
				} else {
					if (value(k) == l_False)
						k = ~k;
					nj.push(k);
					if (!becomes_cycle_source && !sign(k) && defType[var(k)]
							!= NONDEF && scc[v] == scc[var(k)])
						becomes_cycle_source = true;
				}
			}
		} else if (aw.set->type == MIN) {
			int i = 0;
			for (; lits[i].weight < aw.expr->min; ++i) { // NOTE: because v is not false, the test will fail before i==set.size(), and also none of the encountered literals will be true.
				Lit k = lits[i].lit;
				nj.push(~k);
				if (!becomes_cycle_source && sign(k) && defType[var(k)]
						!= NONDEF && scc[v] == scc[var(k)])
					becomes_cycle_source = true;
			}
			for (; value(lits[i].lit) != l_False; ++i)
				; // NOTE: because v is not false, the test will fail before i==set.size()
			Lit k = lits[i].lit;
			nj.push(k);
			if (!becomes_cycle_source && !sign(k) && defType[var(k)] != NONDEF
					&& scc[v] == scc[var(k)])
				becomes_cycle_source = true;
		} else { // MAX
			int i = lits.size() - 1;
			for (; lits[i].weight > aw.expr->max; --i) { // NOTE: because v is not false, the test will fail before i<0, and also none of the encountered literals will be true.
				Lit k = lits[i].lit;
				nj.push(~k);
				if (!becomes_cycle_source && sign(k) && defType[var(k)]
						!= NONDEF && scc[v] == scc[var(k)])
					becomes_cycle_source = true;
			}
			for (; value(lits[i].lit) != l_False; --i)
				; // NOTE: because v is not false, the test will fail before i<0
			Lit k = lits[i].lit;
			nj.push(k);
			if (!becomes_cycle_source && !sign(k) && defType[var(k)] != NONDEF
					&& scc[v] == scc[var(k)])
				becomes_cycle_source = true;
		}

		change_jstfc_aggr(v, nj);
		if (becomes_cycle_source)
			addCycleSource(v);
	}
}

/*
 * Return true if indirectpropagation is necessary
 */
bool TSolver::indirectPropagateNow() {
	if (defn_strategy == always)
		return true;
	// Decide if state is two-valued (then we definitely have to search).
	if (!solver->existsUnknownVar()) {
		if (defn_strategy == lazy)
			return false;
		if (defn_strategy == adaptive && adaption_current < adaption_total) {
			adaption_current++;
			return false;
		}
	}
	return true;
}

/////////////
//Finding unfounded checks by
//Generalized tarjanUFS
//TODObroes voorlopig wordt er nog overal met completion clauses gewerkt, die dus altijd een disjunctie zijn en geordend zoals minisat er zin in heeft, dus checken voor head en dergelijke
//justification is een subgrafe van de dependency grafe
UFS TSolver::visitForUFSgeneral(Var v, Var cs, std::set<Var>& ufs, int visittime, vec<Var>& stack, vec<Var>& root, vec<Var>& visited, vec<bool>& incomp){
	visited[v]=visittime;visittime++;root[v]=v;

	DefType type = defType[v];

	if(type==AGGR){return OLDCHECK;}
	assert(type==CONJ || type==DISJ);

	Clause* c = definition[v];
	//Rule* c = definition[v];

	for(int i=0; i<c->size(); i++){
		DefType childtype = defType[var(c->operator [](i))];
		Lit l = c->operator [](i);
		if(var(l)==v){ continue; } //rule head or identical body atom
		if(childtype==AGGR){return OLDCHECK;}
		if(childtype==NONDEF || scc[var(l)]!=scc[v] || incomp[var(l)] /*|| STILL JUSTIFIED*/){
			if(value(l)!=l_False && type==DISJ){
				incomp[v]=true;
				//change_jstfc_disj(v, l);
				return NOTUNFOUNDED;
			}
		}
	}

	stack.push(v);

	int notunfoundedchildren = 0;
	int totaldefined = 0;
	bool notunfounded = false, stop = false;

	for(int i=0; i<c->size(); i++){
		Var child = var(c->operator [](i));
		if(child==v){continue;}
		if(!(defType[child]==CONJ || defType[child]==DISJ)){continue;}
		totaldefined++;
		if(visited[child]==-1){
			switch(visitForUFSgeneral(child, cs, ufs, visittime, stack, root, visited, incomp)){
			case STILLPOSSIBLE:
				//if CONJ and the child's parent was visited earlier than this node,
				//then return higher, because no other conjunct has to be visited to find a UFS if the loop goes higher
				//if this is the highest visited node, there is a loop which starts here so UFS, so stop
				if(type==CONJ){
					if(visited[root[child]]<visited[v]){
						return STILLPOSSIBLE;
					}else if(visited[root[child]]==visited[v]){
						stop = true;
					}
				}
				break;
			case NOTUNFOUNDED:
				if(type == CONJ){
					notunfoundedchildren++;
				}else{
					//change_jstfc_disj(v, c->operator [](i));
					notunfounded = true;
				}
				break;
			case UFSFOUND:
				return UFSFOUND;
			case OLDCHECK:
				return OLDCHECK;
			}
		}
		if(notunfounded || stop){
			break;
		}
		if(!incomp[child] && visited[root[child]]<visited[v]){
			root[v]=root[child];
		}
	}

	if(type == CONJ && notunfoundedchildren==totaldefined){
		notunfounded = true;
		//do something with justifications for CONJ, or not necessary?
	}

	if(notunfounded){
		//change justification of this node and of anything above x on the stack
		Var x = stack.last();
		while(x!=v){
			incomp[x]=true;
			/*if(defType[x]==DISJ){
				//change the justification randomly to one of the body literals (TODO TODO completely not sure if this is correct!!!!!)
				Queue<Var> q;
				Justify(v, cs, ufs, q);
			}*/
			stack.pop();
			x=stack.last();
		}

		return NOTUNFOUNDED;
	}else {
		if(root[v]==v){
			bool allfalse = true;

			Var x;
			do{
				x = stack.last();
				if(value(x)!=l_False){allfalse = false;}
				ufs.insert(x);
				incomp[x]=true;
				stack.pop();
			}while(x!=v);

			if(allfalse){
				ufs.clear();
				return STILLPOSSIBLE;
			}
			if(ufs.size()>1){
				return UFSFOUND;
			}else{
				int containsx = 0;
				for(int i=0; i<c->size(); i++){
					if(x==var(c->operator [](i))){
						containsx++;
					}
				}
				if(containsx>1){ //there is a loop of length 1, so x itself is an UFS
					return UFSFOUND;
				}else{//no loops, x is only an SCC, not a UFS
					ufs.clear();
					return STILLPOSSIBLE;
				}
			}
		}else{
			return STILLPOSSIBLE;
		}
	}
}

/////
//Justification algorithm
/*
 * Given a tarjan execution and at some a justification is found. How to propagate it through the nodes
 * that have already been visited?
 * Keep track of which nodes have been visited by who. When a supporting justification is found, that has
 * to be followed in the opposite way:
 * if x is the justifying literal, then change the justification of all the nodes who visited (OR CHECKED to visit) x. Queue all
 * those nodes.
 * Then go through the queue, and recursively change the justification of all the nodes who visited the one
 * in the queue to the node chosen from the queue. And add the changed ones to the queue. Keep doing this
 * until the queue is empty. If a justification has already been changed, don't change it again.
 * Check that by keeping an extra justification datastructure, which is copied into sp_just when finished
 *
 * what to do for conjunctions? just skip them
 *
 */

void TSolver::changeJustifications(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& vis, int offset){
	vec<Lit> queue;

	if(!hasJustification(definednode, vis)){
		change_jstfc_disj(definednode, firstjustification);
		vis[definednode]=-vis[definednode]; //set it as justified
		queue.push(Lit(definednode));
	}

	while(queue.size()>0){
		Lit just = queue.last();
		queue.pop();
		for(int i=0; i<network[visitedAt(var(just), vis)].size(); i++){
			Lit t = network[visitedAt(var(just), vis)][i];
			if(!hasJustification(var(t), vis)){
				change_jstfc_disj(var(t), just);
				vis[var(t)]=-vis[var(t)];
				queue.push(t);
			}
		}
	}
}

inline bool TSolver::visitedEarlier(Var x, Var y, vec<Var>& vis){
	int x1 = vis[x]>0?vis[x]:-vis[x];
	int y1 = vis[y]>0?vis[y]:-vis[y];
	return x1<y1;
}

inline bool TSolver::visited(Var x, vec<Var>& vis){
	return vis[x]!=0;
}

inline int TSolver::visitedAt(Var x, vec<Var>& vis){
	return vis[x]>0?vis[x]:-vis[x];
}

inline bool TSolver::hasJustification(Var x, vec<Var>& vis){
	return vis[x]<0;
}

/////////////
//Finding unfounded checks by
//validjust indicates both that the element is already in a justification or is in another found component (in which case it might also be false, not requiring a justification)
UFS TSolver::visitForUFSsimple(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& vis, vec<vec<Lit> >& network, int networkoffset, vec<Var>& tempseen){
	vis[v]=visittime;
	int timevisited = visittime;
	visittime++;
	tempseen.push(v);

	DefType type = defType[v];

	if(type==AGGR){return OLDCHECK;}
	assert(type==CONJ || type==DISJ);

	Clause* c = definition[v];
	//Rule* c = definition[v];
	if(solver->verbosity >=1){
		printClause(*c);
	}

	Lit definedChild;
	bool childfound = false;

	for(int i=0; i<c->size(); i++){
		DefType childtype = defType[var(c->operator [](i))];
		Lit l = c->operator [](i);
		if(var(l)==v){ continue; } //rule head or identical body atom
		if(childtype==AGGR){return OLDCHECK;}
		if(childtype==NONDEF || scc[var(l)]!=scc[v] || hasJustification(var(l), vis)){
			if(value(l)!=l_False && type==DISJ){
				changeJustifications(v, l, network, vis, networkoffset);
				return NOTUNFOUNDED;
			}
		}
		if(type==CONJ){
			if(childfound){
				 definedChild = l;
				 childfound = true;
			}else{
				return OLDCHECK;
			}
		}
	}

	stack.push(v);

	if(type==CONJ){
		if(childfound){

			if(visited(var(definedChild), vis) && network.size()<visittime+1){
				network.growTo(visittime+1);
				network[visittime].push(Lit(v));
			}else{
				network[visitedAt(var(definedChild), vis)].push(Lit(v));
			}

			if(!visited(var(definedChild), vis)){
				UFS ret = visitForUFSsimple(var(definedChild), ufs, visittime, stack, vis, network, networkoffset, tempseen);
				if(ret != STILLPOSSIBLE){
					return ret;
				}
			}
			if(!hasJustification(var(definedChild), vis) && visitedEarlier(var(definedChild), v, vis)){
				vis[v]=vis[var(definedChild)];
			}
		}
	}else{ //DISJ, have returned from all others
		for(int i=0; i<c->size(); i++){
			Var child = var(c->operator [](i));
			if(child==v){ continue;	}
			if(!(defType[child]==CONJ || defType[child]==DISJ)){continue;}

			if(!visited(child, vis) && network.size()<visittime+1){
				network.growTo(visittime+1);
				network[visittime].push(Lit(v));
			}else{
				network[visitedAt(child, vis)].push(Lit(v));
			}

			if(!visited(child, vis)){
				UFS ret = visitForUFSsimple(child, ufs, visittime, stack, vis, network, networkoffset, tempseen);
				if(ret!=STILLPOSSIBLE){
					return ret;
				}
			}
			if(!hasJustification(child, vis) && visitedEarlier(child, v, vis)){
				vis[v]=vis[child];
			}
		}
	}

	if(visitedAt(v, vis)==timevisited){
		bool allfalse = true;
		Var x;
		do{
			x=stack.last();
			stack.pop();
			vis[x]=vis[x]>0?vis[x]:-vis[x];
			ufs.insert(x);
			if(value(x)!=l_False){allfalse = false;}
		}while(x!=v);
		if(allfalse){
			ufs.clear();
			return STILLPOSSIBLE;
		}
		if(ufs.size()>1){
			if(solver->verbosity >=1){
				/*fprintf(stderr, "ufsfound: ");
				for(std::set<Var>::iterator i=ufs.begin(); i!=ufs.end(); i++){
					Var x = *i;
					fprintf(stderr, "%d:%c", x << 1, value(x) == l_True ? '1' : (value(x) == l_False ? '0' : 'X'));
				}*/
			}
			return UFSFOUND;
		}else{
			int containsx = 0;
			for(int i=0; i<c->size(); i++){
				if(x==var(c->operator [](i))){
					containsx++;
				}
			}
			if(containsx>1){ //there is a loop of length 1, so x itself is an UFS
				/*if(solver->verbosity >=1){
					fprintf(stderr, "ufsfound: ");
					for(std::set<Var>::iterator i=ufs.begin(); i!=ufs.end(); i++){
						Var x = *i;
						fprintf(stderr, "%d:%c", x << 1, value(x) == l_True ? '1' : (value(x) == l_False ? '0' : 'X'));
					}
				}*/
				return UFSFOUND;
			}else{//no loops, x is only an SCC, not a UFS
				ufs.clear();
			}
		}
	}

	return STILLPOSSIBLE;
}

int count = 0;

/*_________________________________________________________________________________________________
 |
 |  indirectPropagate : [void]  ->  [Clause*]
 |
 |  Description:
 |    If there is an unfounded set w.r.t. current assignment, this method will find one. There
 |    are then two possible results:
 |    - Making all unfounded set atoms false would result in a conflict. There will be no new
 |      elements on the propagation queue, and the conflicting loop formula is added to the theory
 |      and returned.
 |    - For each atom of the unfounded set a loop formula is added to the theory, and used as
 |      reason clause for making the atom false. Thus the propagation queue is not empty. NULL is
 |      returned.
 |    Otherwise, the justification and the watches will be adjusted and 'aligned', such that the
 |    justification is loop-free.
 |________________________________________________________________________________________________@*/
Clause* TSolver::indirectPropagate() {
	if (!indirectPropagateNow()) {
		return NULL;
	}

	findCycleSources();

	bool ufs_found = false;
	std::set<Var> ufs;

	uint64_t old_justify_calls = justify_calls;
 	int j=0;

 	if(ufs_strategy==depth_first){
 		int visittime = 1;	//time at which NO node has been visited yet
 		vec<Var> stack;
 		/* the seen2 variable is used to indicate:
 		 * 		that a value has been visited (and its number is the time at which it was visited
 		 * 		0 means not yet visited
 		 * 		a negative value means that it has been visited at the abs value and that it has
 		 * 		already received a valid justification
 		 */
 		int offset;
 		vec<Var> tempseen; //used to keep the visited nodes, that have to be reset in seen2

 		for (; !ufs_found && j < css.size(); j++){//hij komt nooit in het geval dat hij iets op de stack moet pushen, altijd disj unfounded???
 			if(isCS[css[j]] && seen[css[j]]==0){
 				//TODO om seen te gebruiken, mag dat niet tegelijk gebruikt kunnen worden in unfounded()

 				//TODO 2: programma goed documenteren en een pseudo code versie bijhouden naast een lijst met optimalisaties
 				vec<vec<Lit> > network;	//maps a node to a list of nodes that have visited the first one
										//as index, the visited time is used

 				//TODO nakijken waarom offset nog misging
 				//offset = visittime-1;
 				//network.growTo(visittime+1-offset);
 				//network[visittime-offset].push(Lit(css[j]));
 				network.growTo(visittime+1);
				network[visittime].push(Lit(css[j]));
 				UFS ret = visitForUFSsimple(css[j], ufs, visittime, stack, seen2, network, offset, tempseen);
 				switch(ret){
 				case UFSFOUND:
 					ufs_found = true;
 					break;
 				case NOTUNFOUNDED:
 					break;
 				case STILLPOSSIBLE:
 					break;
 				case OLDCHECK:
 					ufs_found = unfounded(css[j], ufs);
 					break;
 				}
 			}
 		}
 		for (int i = 0; i < nVars()/*tempseen.size()*/; i++) {
			//seen2[tempseen[i]] = 0;
 			seen2[i] = 0;
		}
 	}else{
 		for (; !ufs_found && j < css.size(); j++){
			if(isCS[css[j]]){
				ufs_found = unfounded(css[j], ufs);
			}
		}
 	}

 	if(verbosity>0 && ufs_found){
		fprintf(stderr, "UFSfound, size %i\n", ufs.size());
	}

	justifiable_cycle_sources += ufs_found ? (j - 1) : j; // This includes those that are removed inside "unfounded".
	succesful_justify_calls += (justify_calls - old_justify_calls); //TODO this is no longer be correct for the tarjan algo

	if (ufs_found) {
		if (verbosity >= 2) {
			reportf("Found an unfounded set of size %d: {",ufs.size());
			for (std::set<Var>::iterator it = ufs.begin(); it != ufs.end(); ++it)
				reportf(" %d",*it+1);
			reportf(" }.\n");
		}
		cycles++;
		cycle_sizes += ufs.size();
		if (defn_strategy == adaptive)
			adaption_current++; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
		return assertUnfoundedSet(ufs);
	} else { // Found a witness justification.
		apply_changes();
		if (defn_strategy == adaptive) {
			if (adaption_current == adaption_total)
				adaption_total++; // Next time, skip one decision level extra.
			else
				adaption_total--;
			if (adaption_total < 0)
				adaption_total = 0;
			adaption_current = 0;
		}
		// fwIndirectPropagate();
		// NB: nb of witnesses found == nb of decisions made in case of "always"
		//if (verbosity>=2) assert(isCycleFree()); // Only debugging! Time consuming.
		return NULL;
	}
}

bool TSolver::unfounded(Var cs, std::set<Var>& ufs) {
	justify_calls++;
	bool rslt = false; // if we go straight to Finish, this will be the result.
	vec<Var> tmpseen; // use to speed up the cleaning of data structures in "Finish"
	Queue<Var> q;
	Var v;
	markNonJustified(cs, tmpseen);
	if (!seen[cs]) {
		isCS[cs] = false;
		goto Finish;
	} // 'seen[v]' means: v has path to cs in current sp_justification.

	q.insert(cs);
	ufs.clear();
	ufs.insert(cs);

	while (q.size() > 0) {
		v = q.peek();
		q.pop();
		if (!seen[v])
			continue;
		if (directlyJustifiable(v, ufs, q))
			if (Justify(v, cs, ufs, q))
				goto Finish;
	}
	assert(ufs.size() > 0); // The ufs atoms form an unfounded set. 'cs' is in it.
	rslt = true;
	Finish: for (int i = 0; i < tmpseen.size(); i++) {
		seen[tmpseen[i]] = 0; /*used_conj[tmpseen[i]].clear(); WITH guards system*/
	}
	return rslt;
}

// Helper for 'unfounded(..)'. True if v can be immediately justified by one change_justification action.
bool TSolver::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q) {
	switch (defType[v]) {
	case CONJ: {
		Clause& c = *definition[v];
		//Rule& c = *definition[v];// NOTE: sign(c[i]) fails for the head literal; for body literals sign is inverted.
		// Find a non-justified body literal, pref. already ufs.
		// - If not found: bottom up propagation
		// - If found: set conjunction's watch to it; make sure it's ufs and on queue.
		int i = 0;
		for (; i < c.size() && !(sign(c[i]) && seen[var(c[i])]); ++i)
			;
		if (i == c.size())
			return true; // Each body literal has either !sign (is negative) or !seen (is justified wrt v).

		/*            // WITH guards system
		 Var candidate = var(c[i]);    // Else: this var is non-justified, but might not be ufs.
		 for (; i<c.size() && !(sign(c[i]) && seen[var(c[i])] && ufs.find(var(c[i])) != ufs.end()); ++i);
		 if (i==c.size()) {
		 ufs.insert(candidate);
		 q.insert(candidate);
		 used_conj[candidate].push(v);
		 } else
		 used_conj[var(c[i])].push(v); // non-justified AND already ufs.
		 */
		// WITHOUT guards system. Use 'seen[v]' as a counter: number of 'seen' body literals!
		seen[v]=0;
		for (; i < c.size(); ++i) {
			Var x = var(c[i]);
			if (seen[x] && sign(c[i])) {
				seen[v]++;
				std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(x);
				if (pr.second)
					q.insert(x);
			}
		}
		break;
	}
	case DISJ: {
		Clause& c = *definition[v];
		//Rule& c = *definition[v];
		// Find a justified non-false body literal.
		// - If found: set watch to it; bottom up propagation
		// - If not found: touch all non-false body literals; add them to queue.
		vec<Var> add_to_q;
		for (int i = 0; i < c.size(); ++i) {
			Lit bdl = c[i];
			Var b = var(bdl);
			if (bdl != Lit(v, true) && value(bdl) != l_False) {
				if (sign(bdl) || !seen[b]) {
					change_jstfc_disj(v, bdl);
					return true; // bad style, but anyway...
				} else
					add_to_q.push(b);
			}
		}
		for (int i = 0; i < add_to_q.size(); ++i) {
			std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(
					add_to_q[i]);
			if (pr.second)
				q.insert(add_to_q[i]);
		}
		break;
	}
	case AGGR: {
		AggrWatch& aw = (Aggr_watches[v])[0];
		vec<AggrSet::WLit>& lits = aw.set->set;
		switch (aw.set->type) {
		case SUM: {
			int min = 0;
			int max = aw.set->cmax;
			bool complete = false;
			vec<Lit> nj;
			vec<Var> add_to_q;
			// Use only negative or justified literals.
			for (int i = 0; !complete && i < lits.size(); ++i) {
				Lit l = lits[i].lit;
				// Note: l_Undef literals may be used twice, once pos and once neg!
				if (value(l) != l_False) {
					if (!sign(l) && seen[var(l)]) {
						if (ufs.find(var(l)) == ufs.end())
							add_to_q.push(var(l));
					} else {
						nj.push(l);
						min += lits[i].weight;
						if (min >= aw.expr->min && max <= aw.expr->max)
							complete = true;
					}
				}
				if (value(l) != l_True) {
					if (sign(l) && seen[var(l)]) {
						if (ufs.find(var(l)) == ufs.end())
							add_to_q.push(var(l));
					} else {
						nj.push(~l);
						max -= lits[i].weight;
						if (min >= aw.expr->min && max <= aw.expr->max)
							complete = true;
					}
				}
			}
			if (complete) {
				change_jstfc_aggr(v, nj);
				return true;
			} else {
				for (int i = 0; i < add_to_q.size(); ++i) {
					q.insert(add_to_q[i]);
					ufs.insert(add_to_q[i]);
				}
			}
			break;
		}
		case PROD: {
			int min = 1;
			int max = aw.set->cmax;
			bool complete = false;
			vec<Lit> nj;
			vec<Var> add_to_q;
			// Use only negative or justified literals.
			for (int i = 0; !complete && i < lits.size(); ++i) {
				Lit l = lits[i].lit;
				if (value(l) != l_False) {
					if (!sign(l) && seen[var(l)]) {
						if (ufs.find(var(l)) == ufs.end())
							add_to_q.push(var(l));
					} else {
						nj.push(l);
						min *= lits[i].weight;
						if (min >= aw.expr->min && max <= aw.expr->max)
							complete = true;
					}
				}
				if (value(l) != l_True) {
					if (sign(l) && seen[var(l)]) {
						if (ufs.find(var(l)) == ufs.end())
							add_to_q.push(var(l));
					} else {
						nj.push(~l);
						max = max / lits[i].weight;
						if (min >= aw.expr->min && max <= aw.expr->max)
							complete = true;
					}
				}
			}
			if (complete) {
				change_jstfc_aggr(v, nj);
				return true;
			} else {
				for (int i = 0; i < add_to_q.size(); ++i) {
					q.insert(add_to_q[i]);
					ufs.insert(add_to_q[i]);
				}
			}
			break;
		}
		case MIN: {
			vec<Var> add_to_q;
			vec<Lit> nj;
			int i = 0;
			for (; lits[i].weight < aw.expr->min; ++i) { // NOTE: these are exactly the same always. Find some way of doing this only the first time.
				Lit l = lits[i].lit;
				nj.push(~l);
				if (sign(l) && seen[var(l)] && scc[v] == scc[var(l)]
						&& ufs.find(var(l)) == ufs.end())
					add_to_q.push(var(l));
			}
			int atqsize = add_to_q.size();
			for (; lits[i].weight <= aw.expr->max; ++i) {
				Lit l = lits[i].lit;
				if (value(l) != l_False) {
					if (!sign(l) && seen[var(l)] && scc[v] == scc[var(l)]
							&& ufs.find(var(l)) == ufs.end())
						add_to_q.push(var(l));
					else {
						nj.push(l);
						break;
					}
				}
			}
			if (lits[i].weight < aw.expr->min) {
				if (atqsize == 0) {
					change_jstfc_aggr(v, nj);
					return true;
				}
			} else
				atqsize = add_to_q.size();
			for (int i = 0; i < atqsize; ++i) {
				q.insert(add_to_q[i]);
				ufs.insert(add_to_q[i]);
			}
			break;
		}
		case MAX: {
			vec<Var> add_to_q;
			vec<Lit> nj;
			int i = lits.size() - 1;
			for (; lits[i].weight > aw.expr->max; --i) { // NOTE: these are exactly the same always. Find some way of doing this only the first time.
				Lit l = lits[i].lit;
				nj.push(~l);
				if (sign(l) && seen[var(l)] && scc[v] == scc[var(l)]
						&& ufs.find(var(l)) == ufs.end())
					add_to_q.push(var(l));
			}
			int atqsize = add_to_q.size();
			for (; lits[i].weight >= aw.expr->min; --i) {
				Lit l = lits[i].lit;
				if (value(l) != l_False) {
					if (!sign(l) && seen[var(l)] && scc[v] == scc[var(l)]
							&& ufs.find(var(l)) == ufs.end())
						add_to_q.push(var(l));
					else {
						nj.push(l);
						break;
					}
				}
			}
			if (lits[i].weight < aw.expr->min) {
				if (atqsize == 0) {
					change_jstfc_aggr(v, nj);
					return true;
				}
			} else
				atqsize = add_to_q.size();
			for (int i = 0; i < atqsize; ++i) {
				q.insert(add_to_q[i]);
				ufs.insert(add_to_q[i]);
			}
			break;
		}
		}
		break;
	}
	default:
		assert(false);
	}

	return false;
}

// Helper for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified.
bool TSolver::Justify(Var v, Var cs, std::set<Var>& ufs, Queue<Var>& q) {
	Queue<Var> tojustify;
	tojustify.insert(v); // ... starting with v.
	while (tojustify.size() > 0) {
		Var k = tojustify.peek();
		tojustify.pop();
		if (seen[k]) { // Prevent infinite loop. NB: 'seen' here is the same as in 'unfounded': means: k has path in sp_justification to cs.
			// Make it justified.
			ufs.erase(k);
			seen[k]=0;
			if (isCS[k]) {
				isCS[k] = false;
				cs_removed_in_justify++;
			}
			if (k == cs)
				return true;

			// Record also disjunctions that now become justified for bottom-up propagation.
			vec<Var>& disjs = disj_occurs[k + k]; // k+k is the index of the positive literal k.
			for (int i = 0; i < disjs.size(); ++i) {
				Var d = disjs[i];
				if (seen[d]) { // && ufs.find(d) != ufs.end()) //   WITH this extra test: only bottom-up propagate in already marked literals.
					change_jstfc_disj(d, Lit(k, false));
					tojustify.insert(d);
				}
			}

			// Record conjunctions that might now be justified on the main queue.
			/*            // WITH guards system
			 vec<Var>& conjs = used_conj[k];
			 for (int i=0; i<conjs.size(); ++i)
			 if (ufs.find(conjs[i]) != ufs.end())
			 q.insert(conjs[i]);
			 */
			// WITHOUT guards system.
			vec<Var>& conjs = conj_occurs[k + k];
			for (int i = 0; i < conjs.size(); ++i) {
				Var c = conjs[i];
				if (seen[c] && ufs.find(conjs[i]) != ufs.end()) { //  NOTE: we use 'seen' as a counter, but the counter is set *only* for literals in ufs. So the extra test is required here.
					if (seen[c] == 1)
						tojustify.insert(c); // Recall that the if-test in the beginning checks whether the atom is 'seen'.
					else
						seen[c]--;
				}
			}

			if (ecnf_mode.aggr) {
				// Record aggregates that might now be justified on the main queue. TODO : can we do this less eagerly? something like used_conjs?
				vec<AggrWatch>& aw = Aggr_watches[k];
				for (int i = 0; i < aw.size(); ++i) {
					if (aw[i].type == DEFN)
						continue;
					vec<AggrExpr*>& exprs = aw[i].set->exprs;
					for (int j = 0; j < exprs.size(); ++j) {
						Var d = var(exprs[j]->c);
						if (seen[d]) //  && ufs.find(d) != ufs.end())  WITH this extra test: only bottom-up propagate in already marked literals.
							q.insert(d);
					}
				}
			}
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void TSolver::change_jstfc_disj(Var v, Lit j) {
	assert(defType[v]==DISJ);
	sp_justification_disj[v] = j;
	changed_vars.push(v);
}

// Change sp_justification: v is now justified by j.
void TSolver::change_jstfc_aggr(Var v, const vec<Lit>& j) {
	// NOTE: maybe more efficient implementation possible if j changes very little from previous justification? Especially for MIN and MAX.
	assert(defType[v]==AGGR);
	sp_justification_aggr[v].clear();
	for (int i = 0; i < j.size(); i++)
		sp_justification_aggr[v].push(j[i]);
	changed_vars.push(v);
}

/**
 * Creates the loop formula given an unfounded set
 */
void TSolver::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf){
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		switch (defType[*tch]) {
		case CONJ:
			break;
		case DISJ:
			{
				Clause& cl = *definition[*tch];
				//Rule& cl = *definition[*tch];
				for (int i = 0; i < cl.size(); i++) {
					Lit l = cl[i];
					if (l != Lit(*tch, true) && seen[var(l)] != (sign(l) ? 1 : 2)
							&& ufs.find(var(cl[i])) == ufs.end()) {
						loopf.push(l);
						seen[var(l)] = (sign(l) ? 1 : 2); // Just in case P and ~P both appear; otherwise we might get something between well-founded and ultimate semantics...
					}
				}
				break;
			}
		case AGGR:
			{
				AggrWatch& aw = (Aggr_watches[*tch])[0];
				vec<AggrSet::WLit>& lits = aw.set->set;
				if (aw.set->type == SUM || aw.set->type == PROD) {
					for (int i = 0; i < lits.size(); ++i) {
						Lit l = lits[i].lit;
						if (value(l) == l_True) {
							if (sign(l) || ufs.find(var(l)) == ufs.end()) {
								loopf.push(l);
								seen[var(l)] = (sign(l) ? 1 : 2);
							}
						} else if (value(l) == l_False) {
							if (~sign(l) || ufs.find(var(l)) == ufs.end()) {
								loopf.push(~l);
								seen[var(l)] = (sign(l) ? 2 : 1);
							}
						}
					}
				} else if (aw.set->type == MIN) {
					int i = 0;
					for (; lits[i].weight < aw.expr->min; ++i) {
						if (ufs.find(var(lits[i].lit)) == ufs.end()) {
							loopf.push(~lits[i].lit);
							seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 2 : 1);
						}
					}
					for (; lits[i].weight <= aw.expr->max; ++i) {
						if (ufs.find(var(lits[i].lit)) == ufs.end()) {
							loopf.push(lits[i].lit);
							seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 1 : 2);
						}
					}
				} else { // MAX
					int i = lits.size() - 1;
					for (; lits[i].weight > aw.expr->max; --i) {
						if (ufs.find(var(lits[i].lit)) == ufs.end()) {
							loopf.push(~lits[i].lit);
							seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 2 : 1);
						}
					}
					for (; lits[i].weight >= aw.expr->min; --i) {
						if (ufs.find(var(lits[i].lit)) == ufs.end()) {
							loopf.push(lits[i].lit);
							seen[var(lits[i].lit)] = (sign(lits[i].lit) ? 1 : 2);
						}
					}
				}
				break;
			}
		}
	}
}

/**
 * If an atom of 'ufs' was already true, return a loop formula for this (one
 * such) atom as conflicting clause.
 * Otherwise, add a loop formula for each atom in ufs, enqueue the negation of
 * each of those atoms, and return NULL.
 * For each atom in UFS that is false, don't do anything
 * TODO don't find UFS that are already completely false
 */
Clause* TSolver::assertUnfoundedSet(const std::set<Var>& ufs) {
	assert(!ufs.empty());

	// Create the loop formula: add the antecedents (first element will be filled in later).
	vec<Lit> loopf(1);
	createLoopFormula(ufs, loopf);

	for (int i = 1; i < loopf.size(); i++){
		seen[var(loopf[i])]=0;
	}
	extdisj_sizes += loopf.size() - 1;

	if (defn_strategy != always) {// Maybe the loop formula could have been derived at an earlier level: in that case we first have to backtrack to that level.
		// Set the backtrack level.
		int lvl = 0;
		for (int i = 1; i < loopf.size(); i++)
			if (solver->getLevel(var(loopf[i])) > lvl)
				lvl = solver->getLevel(var(loopf[i]));
		solver->backtrackTo(lvl);
	}

	// Verify whether a conflict ensues.
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		Var v = *tch;
		if (value(v) == l_True) {
			loopf[0] = Lit(v, true);
			Clause* c = Clause_new(loopf, true);
			solver->addLearnedClause(c);
			if (verbosity >= 2) {
				reportf("Adding conflicting loop formula: [ ");
				printClause(*c);
				reportf("].\n");
			}
			justify_conflicts++;
			return c;
		}
	}

	// No conflict: then enqueue all facts and their loop formulas.
	if (loopf.size() >= 5) { // Then we introduce a new variable for the antecedent part.
        Var v = solver->newVar();
        if (verbosity>=2) {reportf("Adding new variable for loop formulas: %d.\n",v+1);}
        // v \equiv \bigvee\extdisj{L}
        // ~v \vee \bigvee\extdisj{L}.
        loopf[0] = Lit(v,true); Clause* c = Clause_new(loopf, true);
        solver->addLearnedClause(c);
        if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        solver->setTrue(loopf[0], c);
        // \bigwedge_{d\in\extdisj{L}} v \vee ~d.
        vec<Lit> binaryclause(2); binaryclause[0] = Lit(v,false);
        for (int i=1; i<loopf.size(); ++i) {
            binaryclause[1] = ~loopf[i];
            Clause* c = Clause_new(binaryclause, true);
            solver->addLearnedClause(c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }

        // \bigwedge_{l\in L} \neg l \vee v
        binaryclause[1] = Lit(v,false);
        for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
            binaryclause[0] = Lit(*tch,true); Clause* c = Clause_new(binaryclause, true);
            solver->addLearnedClause(c);
            //solver->uncheckedEnqueue(binaryclause[0], c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }
    } else { // We simply add the loop formula as is.
        for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
        	if(solver->value(*tch)==l_Undef){
        		loopf[0] = Lit(*tch,true); Clause* c = Clause_new(loopf, true);
				solver->addLearnedClause(c);
				solver->setTrue(loopf[0], c);
				if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        	}
        }
    }
    return NULL;
}

/* Precondition:  !seen[i] for each i.
 * Postcondition: seen[i]  for exactly those i that are ancestors of cs in sp_justification. If defn_search==stop_at_cs, there should not be other cycle sources then cs in the path from added literals to cs.
 */
void TSolver::markNonJustified(Var cs, vec<Var>& tmpseen) {

	Queue<Var> q;
	markNonJustifiedAddParents(cs, cs, q, tmpseen);
	// Now recursively do the same with each enqueued Var.
	Var x;
	while (q.size() > 0) {
		x = q.peek();
		q.pop();
		markNonJustifiedAddParents(x, cs, q, tmpseen);
	}

	//#define addVar(x)      { if (!seen[x] && (scc[x]==cs_scc)) { seen[x]=1; tmpseen.push(x); q.insert(x); total_marked_size++; } }
	//#define addVarStop(x)  { if (!seen[x] && (scc[x]==cs_scc) && (x==cs || !isCS[x])) { seen[x]=1; tmpseen.push(x); q.insert(x); total_marked_size++; } }
	//#define addParents(x)     { vec<Var>& v = disj_occurs[x+x]; for (int i=0; i<v.size(); ++i) { if (var(sp_justification_disj[v[i]])==x) { Var y=v[i]; addVar(y); } } vec<Var>& w = conj_occurs[x+x]; for (int i=0; i<w.size(); i++) {Var y=w[i]; addVar(y);} }
	//#define addParentsStop(x) { vec<Var>& v = disj_occurs[x+x]; for (int i=0; i<v.size(); ++i) { if (var(sp_justification_disj[v[i]])==x) { Var y=v[i]; addVarStop(y); } } vec<Var>& w = conj_occurs[x+x]; for (int i=0; i<w.size(); i++) {Var y=w[i]; addVarStop(y);} }
	//NOTE: error in here--cf. markNonJustifiedAddParents#define addAllParents(x)      { vec<Var>& v = disj_occurs[x+x]; for (int i=0; i<v.size(); ++i) { if (var(sp_justification_disj[v[i]])==x) { Var y=v[i]; addVar(y); } } vec<Var>& w = conj_occurs[x+x]; for (int i=0; i<w.size(); i++) { Var y=w[i]; addVar(y); } vec<AggrWatch>& aw = Aggr_watches[x]; for (int i=0; i<aw.size(); i++) { if (aw[i].type==DEFN) continue; Var y=var(aw[i].expr->c); if (!seen[y] && (scc[y]==cs_scc)) { vec<Lit>& jstfc = sp_justification_aggr[y]; for (int j=0; j<jstfc.size(); j++) { if (jstfc[j]==Lit(x,false)) { seen[y]=1; tmpseen.push(y); q.insert(y); total_marked_size++; break; } } } } }
	//SAME HERE.#define addAllParentsStop(x)  { vec<Var>& v = disj_occurs[x+x]; for (int i=0; i<v.size(); ++i) { if (var(sp_justification_disj[v[i]])==x) { Var y=v[i]; addVarStop(y); } } vec<Var>& w = conj_occurs[x+x]; for (int i=0; i<w.size(); i++) {Var y=w[i]; addVarStop(y);} vec<AggrWatch> & aw = Aggr_watches[x]; for (int i=0; i<aw.size(); i++) { if (aw[i].type==DEFN) continue; Var y=var(aw[i].expr->c); if (!seen[y] && (scc[y]==cs_scc)) { vec<Lit> & jstfc = sp_justification_aggr[y]; for (int j=0; j<jstfc.size(); j++) { if (jstfc[j]==Lit(x,false)) { seen[y]=1; tmpseen.push(y); q.insert(y); total_marked_size++; break; } } } } }
	//
	//    Queue<Var> q;
	//    int cs_scc = scc[cs];
	//
	//    if (ecnf_mode.aggr) {
	//        if (defn_search==include_cs) {
	//            // Add parents of cs.
	//            addAllParents(cs);
	//            // Now recursively do the same with each enqueued Var.
	//            Var x;
	//            while (q.size() > 0) {
	//                x = q.peek(); q.pop();
	//                addAllParents(x);
	//            }
	//        } else { // stop_at_cs
	//            addAllParentsStop(cs);
	//            // Now recursively do the same with each enqueued Var.
	//            Var x;
	//            while (q.size() > 0) {
	//                x = q.peek(); q.pop();
	//                addAllParentsStop(x);
	//            }
	//        }
	//    } else {
	//        if (defn_search==include_cs) {
	//            // Add parents of cs.
	//            addParents(cs);
	//            // Now recursively do the same with each enqueued Var.
	//            Var x;
	//            while (q.size() > 0) {
	//                x = q.peek(); q.pop();
	//                addParents(x);
	//            }
	//        } else { // stop_at_cs
	//            addParentsStop(cs);
	//            // Now recursively do the same with each enqueued Var.
	//            Var x;
	//            while (q.size() > 0) {
	//                x = q.peek(); q.pop();
	//                addParentsStop(x);
	//            }
	//        }
	//    }
}

void TSolver::markNonJustifiedAddVar(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
	if (!seen[v] && (scc[v] == scc[cs]) && (defn_search == include_cs || v == cs || !isCS[v])) {
		seen[v] = 1;
		tmpseen.push(v);
		q.insert(v);
		total_marked_size++;
	}
}

void TSolver::markNonJustifiedAddParents(Var x, Var cs, Queue<Var> &q,
		vec<Var>& tmpseen) {
	vec<Var>& v = disj_occurs[x + x];
	for (int i = 0; i < v.size(); ++i){
		if (var(sp_justification_disj[v[i]]) == x){
			markNonJustifiedAddVar(v[i], cs, q, tmpseen);
		}
	}
	vec<Var>& w = conj_occurs[x + x];
	for (int i = 0; i < w.size(); i++){
		markNonJustifiedAddVar(w[i], cs, q, tmpseen);
	}
	if (ecnf_mode.aggr) {
		vec<AggrWatch>& aw = Aggr_watches[x];
		for (int i = 0; i < aw.size(); i++) {
			if (aw[i].type != DEFN) { // Else x is the head, hence not used in the justification.
				for (int j = 0; j < aw[i].set->exprs.size(); j++) {
					Var y = var(aw[i].set->exprs[j]->c); // Find the head of the aggregate expression where x is watched in the body.
					vec<Lit>& jstfc = sp_justification_aggr[y];
					int k = 0;
					for (; k < jstfc.size() && jstfc[k] != Lit(x, false); k++)
						;
					if (k < jstfc.size()) // Found that x is actually used in y's justification.
						markNonJustifiedAddVar(y, cs, q, tmpseen);
				}
			}
		}
	}
}

Clause* TSolver::aggrEnqueue(Lit p, AggrReason* ar) {
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

void TSolver::addSet(int set_id, vec<Lit>& lits, vec<int>& weights) {
	if (!ecnf_mode.aggr)
		reportf("ERROR! Attempt at adding aggregate set, though ECNF specifiers did not contain \"aggr\".\n"), exit(
				3);
	if (lits.size() == 0) {
		reportf("Error: Set nr. %d is empty,\n",set_id);
		exit(3);
	}
	assert(lits.size()==weights.size());
	// Find out if lits contains any doubles.
	vec<Lit> ps(lits.size());
	for (int i = 0; i < lits.size(); i++)
		ps[i] = lits[i];
	sort(ps);
	Lit p;
	int i;
	for (i = 0, p = lit_Undef; i < ps.size(); i++)
		if (ps[i] == p || ps[i] == ~p)
			reportf("ERROR! (W)Set %d contains the same literal twice.\n",set_id), exit(
					3);
		else
			p = ps[i];
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

 NOTE: do not set "ecnf_mode.aggr=true" yet!! Then it will already
 propagate, but in that case the constraint that each derived literal is
 added only once to the queue would be required (otherwise "trues" and
 "falses" get too many counts.)
 */
void TSolver::addAggrExpr(int defn, int set_id, int min, int max, AggrType type) {
	if (!ecnf_mode.aggr)
		reportf("ERROR! Attempt at adding aggregate expression, though ECNF specifiers did not contain \"aggr\".\n"), exit(
				3);

	if (set_id * NB_AGGR_TYPES > aggr_sets.size()) {
		reportf("Error: Set nr. %d is used, but not defined yet.\n",set_id), exit(
				3);
	}
	if (min < 0 || min > max) {
		reportf("Error: aggregate expression with minimum %d and maximum %d is not valid.\n",min,max), exit(
				3);
	}

	Lit c = Lit(defn, false);
	defType[var(c)] = AGGR;
	//TODObroes add if really usefull varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.
	if (ecnf_mode.def)
		defdVars.push(var(c));
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

Clause* TSolver::Aggr_propagate(Lit p) { // TODO: do something about double work? E.g. first propagation head->some body literal, then backward again...
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

Clause* TSolver::Aggr_propagate(AggrSet& as, AggrExpr& ae) {
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
/* (@&) if there is but one remaining non-false literal with weight <= ae.max, that literal has to be made true.
 Lit candidate; bool use_candidate=true;
 for (int u=0;confl==NULL && u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight<=ae.max) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));

 as.set[as.max].weight <= ae.max and there is but one non-false literal with weight < ae.min, that literal has to become true.
 if (as.max<=ae.max) {
 Lit candidate; bool use_candidate=true;
 for (int u=0;u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight<ae.min) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));
 }

 if there is but one remaining non-false literal with weight >= ae.min, that literal has to be made true.
 Lit candidate; bool use_candidate=true;
 for (int u=0;confl==NULL && u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight>=ae.min) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));

 as.set[as.max].weight <= ae.max and there is but one non-false literal with weight < ae.min, that literal has to become true.
 if (as.min>=ae.min) {
 Lit candidate; bool use_candidate=true;
 for (int u=0;u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight>ae.max) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));
 }
 */

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
Clause* TSolver::getExplanation(Lit p) {
	assert(ecnf_mode.aggr);
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

bool TSolver::isCycleFree() { // currently only when no recursice aggregates!! TODO
    if (!ecnf_mode.def)
        return true;

    assert(!ecnf_mode.aggr);

    reportf("Showing cf- and sp-justification for disjunctive atoms. <<<<<<<<<<\n");
    for (int i = 0; i < nVars(); i++) {
        if (defType[i]==DISJ) {
            printLit(Lit(i,false)); reportf(" <- ");
            printLit(cf_justification_disj[i]);
            reportf("(cf); ");
            printLit(sp_justification_disj[i]);
            reportf("(sp)\n");
        }
    }
    reportf(">>>>>>>>>>\n");

    // Verify cycles.
    vec<int> isfree; // per variable. 0 = free, >0 = number of literals in body still to be justified.
    vec<Lit> justified;
    int cnt_nonjustified = 0;
    for (int i=0;i<nVars();++i) {
        justified.push(Lit(i,true)); // negative literals are justified anyhow.
        if (defType[i]==NONDEF) {
            isfree.push(0);
            justified.push(Lit(i,false));
        } else {
            ++cnt_nonjustified;
            isfree.push(defType[i]==CONJ ? (definition[i]->size()-1) : 1);
        }
    }
    assert(cnt_nonjustified>0);

    int idx=0;
    while (cnt_nonjustified>0 && idx<justified.size()) {
        Lit l = justified[idx++];

        // Occurrences as justifying literal.
        vec<Var>& ds = disj_occurs[toInt(l)];
        vec<Var>& cs = conj_occurs[toInt(l)];

        for (int i=0;i<ds.size();++i) {
            Var d = ds[i];
            if (cf_justification_disj[d]==l) {
                assert(isfree[d]==1);
                isfree[d]=0;
                justified.push(Lit(d,false));
                --cnt_nonjustified;
            }
        }
        for (int i=0;i<cs.size();++i) {
            Var c = cs[i];
            isfree[c]--;
            if (isfree[c]==0) {
                justified.push(Lit(c,false));
                --cnt_nonjustified;
            }
        }
    }

    if (cnt_nonjustified>0) {
        reportf("WARNING: There remain %d literals non-justified.\n",cnt_nonjustified);

        vec<bool> printed; printed.growTo(nVars(),false);
        int i=0;
        while (i<nVars()) {
            reportf("Cycle:\n");
            for (;i<nVars() && (defType[i]==NONDEF || isfree[i]==0);i++) ;
            if (i<nVars()) {
                vec<Var> cycle;
                cycle.push(i);
                int idx=0;
                while (idx<cycle.size()) {
                    Var v = cycle[idx++];
                    if (defType[v]==DISJ) {
                        reportf("D %d justified by ",v+1); printLit(cf_justification_disj[v]); reportf(".\n");
                        if (!printed[var(cf_justification_disj[v])])
                            cycle.push(var(cf_justification_disj[v]));
                    } else {
                        reportf("C %d has",v+1);
                        Clause& c = *definition[v];
                        //Rule& c = *definition[v];
                        for (int j=0; j<c.size(); j++) {
                            Var vj = var(c[j]);
                            if (c[j]!=Lit(v,false) && sign(c[j]) && (isfree[vj]!=0 || printed[vj])) {
                                reportf(" %d",vj+1);
                                if (!printed[vj])
                                    cycle.push(vj);
                            }
                        }
                        reportf(" in its body.\n");
                    }
                    printed[v]=true;
                }
                for (int j=0;j<cycle.size();j++)
                    isfree[cycle[j]]=0;
            }
        }
    } else
        reportf("OK; cf_justification is cycle free.\n");
    return cnt_nonjustified==0;
}

inline void TSolver::apply_changes() {
    for (int i=changed_vars.size()-1; i>=0; i--) {
        Var v = changed_vars[i];
        if (!seen[v]) {
            if (defType[v]==DISJ) cf_justification_disj[v] = sp_justification_disj[v];
            else {
                assert(defType[v]==AGGR);
                vec<Lit>& sp = sp_justification_aggr[v];
                vec<Lit>& cf = cf_justification_aggr[v];
                cf.clear();
                for (int j=0; j<sp.size(); ++j) cf.push(sp[j]);
            }
            seen[v]=1;
        }
    }
    for (int i=0; i<changed_vars.size(); i++)
    	seen[changed_vars[i]]=0;
    changed_vars.clear();
}

inline void TSolver::clear_changes() {
    for (int i=changed_vars.size()-1; i>=0; i--) {
        Var v = changed_vars[i];
        if (!seen[v]) {
            if (defType[v]==DISJ) sp_justification_disj[v] = cf_justification_disj[v];
            else {
                assert(defType[v]==AGGR);
                vec<Lit>& sp = sp_justification_aggr[v];
                vec<Lit>& cf = cf_justification_aggr[v];
                sp.clear();
                for (int j=0; j<cf.size(); ++j) sp.push(cf[j]);
            }
        }
    }
    for (int i=0; i<changed_vars.size(); i++)
    	seen[changed_vars[i]]=0;
    changed_vars.clear();
}

//=================================================================================================
// Debug + etc:
// a literal is a variable shifted one to the left
// a variable is a literal shifted one to the right

inline void TSolver::printLit(Lit l)
{
    solver->printLit(l);
}


template<class C>
inline void TSolver::printClause(const C& c)
{
    solver->printClause(c);
}

inline void TSolver::printRule(const Rule& c)
{
    for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}

inline void TSolver::printAggrSet(const AggrSet& as)
{
    for (int i=0; i<as.set.size(); ++i) {
        reportf(" "); printLit(as.set[i].lit); reportf("(%d)",as.set[i].weight);
    }
}

inline void TSolver::printAggrExpr(const AggrExpr& ae, const AggrSet& as)
{
    printLit(ae.c); reportf(" <- %d <= %s{",ae.min, as.type==SUM ? "sum" : (as.type==PROD ? "prod" : (as.type==MIN ? "min" : "max")));
    printAggrSet(as);
    reportf(" } <= %d. Known values: min=%d, max=%d\n",ae.max,as.min,as.max);
}
