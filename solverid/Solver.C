/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

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

#include "Solver.h"
#include "Sort.h"
#include "Map.h"
#include <cmath>


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters: (formerly in 'SearchParams')
    var_decay(1 / 0.95), clause_decay(1 / 0.999), random_var_freq(0.02)
  , restart_first(100), restart_inc(1.5), learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // More parameters:
    //
  , expensive_ccmin  (true)
  , polarity_mode    (polarity_false)
  , verbosity        (0)
  , defn_strategy    (always)
  , defn_search      (include_cs)
  , adaption_total   (0)
  , adaption_current (0)
  , maxruntime       (0.0)

    // Statistics: (formerly in 'SolverStats')
    //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , prev_conflicts(-1) /*first time test (prev_conflicts==conflicts) should fail*/, cycle_sources(0), justifiable_cycle_sources(0), cycles(0), cycle_sizes(0), justify_conflicts(0) // ecnf_mode.def
  , amo_statements(0), amo_literals(0)                                                             // ecnf_mode.amo
  , nb_times_findCS(0), justify_calls(0), cs_removed_in_justify(0), succesful_justify_calls(0), extdisj_sizes(0)
  , total_marked_size(0)
//  , fw_propagation_attempts(0), fw_propagations(0)

  , ok               (true)
  , cla_inc          (1)
  , var_inc          (1)
  , qhead            (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , random_seed      (91648253)
  , progress_estimate(0)
  , remove_satisfied (true)
{}


Solver::~Solver()
{
    for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    reason    .push(NULL);
    assigns   .push(toInt(l_Undef));
    level     .push(-1);
    activity  .push(0);
    seen      .push(0);

    polarity    .push((char)sign);
    decision_var.push((char)dvar);

    if (ecnf_mode.def) {
        defType.push(NONDEF);
        definition.push(NULL);
        disj_occurs.growTo(2*nVars()); // May be tested on in findCycleSources().
        conj_occurs.growTo(2*nVars()); // Probably not needed anyway...
    }
    if (ecnf_mode.aggr) {
        Aggr_watches.push();
        aggr_reason.push();
    }
    if (ecnf_mode.amo) {
        AMO_watches.growTo(2*nVars());
    }

    insertVarOrder(v);
    return v;
}


bool Solver::addClause(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);

    if (!ok)
        return false;
    else{
        // Check if clause is satisfied and remove false/duplicate literals:
        sort(ps);
        Lit p; int i, j;
        for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
            if (value(ps[i]) == l_True || ps[i] == ~p)
                return true;
            else if (value(ps[i]) != l_False && ps[i] != p)
                ps[j++] = p = ps[i];
        ps.shrink(i - j);
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        assert(value(ps[0]) == l_Undef);
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == NULL);
    }else{
        Clause* c = Clause_new(ps, false);
        clauses.push(c);
        attachClause(*c);
    }

    return true;
}

// First literal in ps is head atom.
bool Solver::addRule(const bool conj, vec<Lit>& ps) {
    if (!ecnf_mode.def)
        reportf("ERROR! Attempt at adding rule, though ECNF specifiers did not contain \"def\".\n"), exit(3);
    assert(decisionLevel() == 0);
    assert(ps.size() > 0); assert(!sign(ps[0]));

    if (!ok)
        return false;
    else{
        if (conj || ps.size()==2)
            for (int i=1; i < ps.size(); i++)
                ps[i]=~ps[i];
        else
            ps[0]=~ps[0];
        // Remark: simplifying clause might be incorrect!
    }

    if (ps.size() == 1){
        // Remark: disjunctive rule with empty body: head is false!
        if (value(ps[0]) == l_False)
            return ok = false;
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == NULL);
    }else{
        Clause* c = Clause_new(ps, false);
        clauses.push(c);
        attachClause(*c);
        Var v=var(ps[0]);
        defdVars.push(v);
        defType[v]=conj?CONJ:DISJ;
        definition[v]=c;

        vec<Lit> binclause(2);
        binclause[0]=~ps[0];
        for (int i=1; i < ps.size(); i++){
            binclause[1]=~ps[i];
            c = Clause_new(binclause, false);
            clauses.push(c);
            attachClause(*c);
        }
    }

    return true;
}

bool Solver::addAMO(vec<Lit>& ps) {
    if (!ecnf_mode.amo)
        reportf("ERROR! Attempt at adding at-most-one statement, though ECNF specifiers did not contain \"eu\" or \"amo\".\n"), exit(3);
    assert(decisionLevel() == 0);
    assert(ps.size() > 0); assert(!sign(ps[0]));

    // Main calls first "addClause(vec<Lit>& ps)", where sorting etc happens. Thus, if we get here, ps has size > 0, and is sorted. If ps.size()==1, the propagation has already happened.
    if (!ok)
        return false;
    if (ps.size() == 1)
        return true;
    Clause* c;
    if (ps.size() == 2){
        ps[0]=~ps[0]; ps[1]=~ps[1];
        c = Clause_new(ps, false);
        clauses.push(c);
        attachClause(*c);
        ps[0]=~ps[0]; ps[1]=~ps[1]; // return ps to its original state: may be used to add Clause (for EU)
    }else{
        // TODO: it should be possible, in case of an EU expression, to use the clause that's already there. Then when a literal becomes true, it can be set as watch in the clause also.
        c = Clause_new(ps, false);
        clauses.push(c);
        attachClause(*c);
        if (verbosity>=2) {reportf("AMO clause: "); printClause(*c); reportf("\n");}

        int n=2*nVars();
        while (n >= AMO_watches.size()) AMO_watches.push(); // Make sure the AMO_watches array is big enough.

        for (int i=0;i<ps.size();i++)
            AMO_watches[toInt(ps[i])].push(c);
        amo_statements++;
        amo_literals += ps.size();
    }

    return true;
}

void Solver::attachClause(Clause& c) {
    assert(c.size() > 1);
    watches[toInt(~c[0])].push(&c);
    watches[toInt(~c[1])].push(&c);
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(Clause& c) {
    assert(c.size() > 1);
    assert(find(watches[toInt(~c[0])], &c));
    assert(find(watches[toInt(~c[1])], &c));
    remove(watches[toInt(~c[0])], &c);
    remove(watches[toInt(~c[1])], &c);
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(Clause& c) {
    detachClause(c);
    free(&c); }


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }

// Can be used to go beyond level 0!
void Solver::cancelFurther(int init_qhead) {

    for (int c = trail.size()-1; c >= init_qhead; c--){
        Var     x  = var(trail[c]);
        assigns[x] = toInt(l_Undef);
        insertVarOrder(x); 
        
        if (!ecnf_mode.init && ecnf_mode.aggr) {
            // Fix the Aggregate min and max values.
            Lit l = trail[c];
            if (aggr_reason[var(l)]!=NULL) {delete aggr_reason[var(l)]; aggr_reason[var(l)]=NULL;}
            vec<AggrWatch>& vcw = Aggr_watches[var(l)];
            for (int i=0; i<vcw.size(); i++) {
                if (vcw[i].set->stack.size()==0 || var(l)!=var(vcw[i].set->stack.last().lit)) // l hadn't yet propagated.
                    continue;
                AggrSet::PropagationInfo pi = vcw[i].set->stack.last();
                vcw[i].set->stack.pop();
                Occurrence tp = relativeOccurrence(vcw[i].type,l);
                assert(tp == pi.type);
                if (tp==DEFN) // These propagations don't affect 'min' and 'max'.
                    continue;
                bool trues = tp==POS;
                switch (vcw[i].set->type) {
                    case SUM:
                        if (trues) vcw[i].set->min-=vcw[i].set->set[vcw[i].index].weight;
                        else       vcw[i].set->max+=vcw[i].set->set[vcw[i].index].weight;
                        break;
                    case PROD:
                        if (trues) vcw[i].set->min=vcw[i].set->min/vcw[i].set->set[vcw[i].index].weight;
                        else       vcw[i].set->max*=vcw[i].set->set[vcw[i].index].weight;
                        break;
                    case MIN:
                        if (trues)
                            while (vcw[i].set->max<vcw[i].set->set.size() && value(vcw[i].set->set[vcw[i].set->max].lit)!=l_True) vcw[i].set->max++;
                        else if (vcw[i].set->set[pi.weight].weight <= vcw[i].set->set[vcw[i].set->min].weight) // TODO PropagationInfo should have "index" too!
                            while (vcw[i].set->min>=0 && vcw[i].set->set[vcw[i].set->min].lit!=~pi.lit) vcw[i].set->min--;

                        break;
                    case MAX:
                        if (trues)
                            while (vcw[i].set->min>=0 && value(vcw[i].set->set[vcw[i].set->min].lit)!=l_True) vcw[i].set->min--;
                        else if (vcw[i].set->set[pi.weight].weight >= vcw[i].set->set[vcw[i].set->max].weight)
                            while (vcw[i].set->max<vcw[i].set->set.size() && vcw[i].set->set[vcw[i].set->max].lit!=~pi.lit) vcw[i].set->max++;
                        break;
                    default:
                        assert(false);
                        break;
                }
            }
        }        
    }

    qhead = init_qhead;
    trail.shrink(trail.size()-qhead);
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        cancelFurther(trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }

//=================================================================================================
// SAT(ID) additional methods

// Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
void Solver::finishECNF_DataStructures() {

    if (ecnf_mode.amo) {
        if (verbosity>=1)
            reportf("| Number of at-most-one statements: %5d",(int)amo_statements);
        if (amo_statements>0) {
            if (verbosity>=1)
                reportf(", avg. size: %7.2f literals.       |\n",(double)amo_literals/(double)amo_statements);
            int n=2*nVars();
            while (n >= AMO_watches.size()) AMO_watches.push();
        } else {
            ecnf_mode.amo=false;
            if (verbosity>=1) {
                reportf("                                     |\n");
                reportf("|    (there will be no at-most-one propagations)                              |\n");
            }
        }
    }

    if (ecnf_mode.aggr) {
        if (verbosity>=1)
            reportf("| Number of aggregate exprs.: %4d",aggr_exprs.size());
        if (aggr_exprs.size()==0) {
            ecnf_mode.aggr=false;
            if (verbosity>=1) {
                reportf("                                            |\n");
                reportf("|    (there will be no aggregate propagations)                                |\n");
            }
        } else {
            int total_nb_set_lits=0;
            for (int i=0; i<aggr_sets.size(); i+=NB_AGGR_TYPES)
                total_nb_set_lits+=aggr_sets[i]->set.size();
            if (verbosity>=1)
                reportf(", over %4d sets, avg. size: %7.2f lits.  |\n",aggr_sets.size()/NB_AGGR_TYPES,(double)total_nb_set_lits/(double)(aggr_sets.size()/NB_AGGR_TYPES));
            // Now do the initial propagations based on set literals that already have a truth value.
            // Note: this is based on the fact that until now ecnf_mode.init=false.
            Clause * confl = NULL;
            for (int i=0; i<qhead && confl==NULL; ++i) // from qhead onwards will still be propagated by simplify().
                confl = Aggr_propagate(trail[i]);
            if (confl!=NULL) {ok=false; return;}
        }
    }

    if (ecnf_mode.def) {
        if (verbosity>=1)
            reportf("| Number of rules           : %6d                                          |\n",defdVars.size());

        remove_satisfied = false; // Satisified clauses that originate in rules might still be needed for correctness.

        // ****** Based on this, initialize "scc". ******
        scc.growTo(nVars(),0);
        vec<int> & root = scc;
        vec<bool> incomp(nVars(),false);
        vec<int> stack;
        vec<int> visited(nVars(),0); // =0 represents not visited; >0 corresponds to a unique value (the counter).
        int counter = 1;

        for (int i=0; i<nVars(); i++)
            if (defType[i]!=NONDEF && visited[i]==0) visit(i,root,incomp,stack,visited,counter);

        // Based on "scc", determine which atoms should actually be considered defined. Meanwhile initialize "disj_occurs" and "conj_occurs".
        // NOTE: because we've searched scc's in the *positive* dependency graph, rules like  P <- ~Q, Q <- ~P will be marked NONDEF here. Hence final well-foundedness check needs to check in defdVars.
        atoms_in_pos_loops = 0;
        disj_occurs.growTo(2*nVars());
        conj_occurs.growTo(2*nVars());
        Lit l; Lit jstf;
        for (int i=0; i<defdVars.size(); ++i) {
            Var v = defdVars[i];
            bool isdefd=false;
            switch (defType[v]) {
                case DISJ:{
                    Clause& dfn=*definition[v];
                    for (int j=0; j<dfn.size(); ++j) {
                        l = dfn[j];
                        if (l!=Lit(v,true))
                            disj_occurs[toInt(l)].push(v);
                        if (!sign(l) && scc[v] == scc[var(l)])
                            isdefd = true;
                    }
                    break;}
                case CONJ:{
                    Clause& dfn=*definition[v];
                    for (int j=0; j<dfn.size(); ++j) {
                        l = ~dfn[j];
                        if (l!=Lit(v,true))
                            conj_occurs[toInt(l)].push(v);
                        if (!sign(l) && scc[v] == scc[var(l)])
                            isdefd = true;
                    }
                    break;}
                case AGGR:{
                    assert(ecnf_mode.aggr);
                    AggrWatch& aw = (Aggr_watches[v])[0];
                    for (int j=0; !isdefd && j<aw.set->set.size(); ++j)
                        if (scc[v] == scc[var(aw.set->set[j].lit)]) // NOTE: disregard sign here: set literals can occur both pos and neg in justifications. This could possibly be made more precise for MIN and MAX...
                            isdefd = true;
                    break;}
                default:
                    assert(false);
            }
            if (isdefd)
                atoms_in_pos_loops++;
            else
                defType[v]=NONDEF; // NOTE: no reason to set definition[v]=NULL.
        }
        if (verbosity>=1)
            reportf("| Number of recursive atoms : %6d                                          |\n",(int)atoms_in_pos_loops);
        if (atoms_in_pos_loops==0) {
            ecnf_mode.def=false;
            if (verbosity>=1)
                reportf("|    (there will be no definitional propagations)                             |\n");
        }

        if (ecnf_mode.def) {
            isCS.growTo(nVars(),false);
            // used_conj.growTo(nVars()); WITH guards system.
        }
        // TODO verify whether there could still be propagations pending due to the fact that rules are not simplified while parsing.

		//Dit verhoogt heel erg de snelheid op sokobans en dergelijke, maar in combinatie met aggregaten gaat het verkeerd
		//TODO do something smarter for aggregates
		if(!ecnf_mode.aggr){
			for (int i=0; i<nVars(); i++){
				if (value(i) != l_Undef){
					solver->addToTrail(Lit(i,(value(i)==l_False)));
				}
			}
		}
    }
}

void Solver::visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter) {
    assert(defType[i]!=NONDEF); assert(!incomp[i]);
    visited[i]=++counter; 
    root[i] = i;
    stack.push(i);
#define recursiveCall(chd,prnt)     {if (visited[chd]==0) visit(chd,root,incomp,stack,visited,counter); if (!incomp[chd] && visited[root[prnt]]>visited[root[chd]]) root[prnt] = root[chd]; }
    switch (defType[i]) {
        case DISJ:{
            for (int j=0; j<definition[i]->size(); ++j) {
                Lit l = (*definition[i])[j]; int w=var(l);
                if (defType[w]!=NONDEF && i!=w && !sign(l)) {recursiveCall(w,i);}
            }
            break;}
        case CONJ:{
            for (int j=0; j<definition[i]->size(); ++j) {
                Lit l = (*definition[i])[j]; int w=var(l);
                if (defType[w]!=NONDEF && i!=w && sign(l))  {recursiveCall(w,i);}
            }
            break;}
        case AGGR:{
            AggrWatch& aw=(Aggr_watches[i])[0];
            for (int j=0; j<aw.set->set.size(); ++j) {
                Var w = var(aw.set->set[j].lit);
                if (defType[w]!=NONDEF)                     {recursiveCall(w,i);}
            }
            break;}
        default:
            assert(false);
    }
    if (root[i]==i) {
        int w;
        do {
            w=stack.last(); stack.pop();
            root[w] = i;
            incomp[w]=true;
        } while(w!=i);
    }
}

/* Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void Solver::findCycleSources() {
    clearCycleSources();
    clear_changes();
    if (prev_conflicts==conflicts && defn_strategy==always && decisionLevel()!=0) {
        for (int i=trail_lim.last(); i<trail.size(); i++) {
            Lit l = trail[i]; // l became true, ~l became false.
            vec<Var>& ds = disj_occurs[toInt(~l)];
            for (int j=0; j<ds.size(); j++) {
                Var v = ds[j];
                if (value(v)!=l_False && cf_justification_disj[v]==~l) // No support anymore; it has to change.
                    findCycleSources(v);
            }
            if (ecnf_mode.aggr) {
                // Aggr_watches[v] is a list of sets in which v occurs (each AggrWatch says: which set, what type of occurrence).
                // If defType[v]==AGGR, (Aggr_watches[v])[0] has type==DEFN and expr->c==Lit(v,false).
                vec<AggrWatch>& as = Aggr_watches[var(l)];
                for (int j=0; j<as.size(); j++) {
                    AggrWatch& aw = as[j];
                    if (aw.type!=DEFN) { // ~l is possibly used in the defining atom's cf_justification.
                        for (int e=0; e<aw.set->exprs.size(); e++) {
                            Lit defn = aw.set->exprs[e]->c;
                            //Lit defn = aw.expr->c;
                            if (value(defn)!=l_False) {
                                vec<Lit>& cf = cf_justification_aggr[var(defn)];
                                int k=0; for (; k<cf.size() && cf[k]!=~l; k++);
                                if (k<cf.size()) // ~l is indeed used in the cf_justification.
                                    findCycleSources(var(defn));
                            }
                        }
                    }
                }
            }
        }
    } else {
        // NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
        prev_conflicts=conflicts;
        for (int i=0; i<defdVars.size(); i++) {
            Var v = defdVars[i];
            if (defType[v]==DISJ) {
                if (value(v)!=l_False && value(cf_justification_disj[v])==l_False)
                    findCycleSources(v);
            } else if (defType[v]==AGGR) {
                if (value(v)==l_False) continue;
                vec<Lit>& cf = cf_justification_aggr[v];
                int k=0; for (; k<cf.size() && value(cf[k])!=l_False; k++);
                if (k<cf.size()) // There is a false literal in the cf_justification.
                    findCycleSources(v);
            }
        }
    }
    nb_times_findCS++;
    cycle_sources+=css.size();
    if (verbosity>=2) {reportf("Indirect propagations. Verifying %d cycle sources:",css.size()); for (int i=0;i<css.size();++i) reportf(" %d",css[i]+1); reportf(".\n");}
}

// Precondition: V is of type DISJ or AGGR. It is non-false, and its cf_justification does not support it.
// Postcondition: sp_justification..[v] supports v. v is added a cycle source if necessary (i.e., if there might be a cycle through its sp_justification).
void Solver::findCycleSources(Var v) {
    if (isCS[v])
        return;
    if (defType[v]==DISJ) {
        Clause& c = *definition[v];
        Lit jstf = c[ c[0]==Lit(v,true)?1:0 ]; // We will use this literal as the supporting literal.
        assert(value(jstf)!=l_False);
        change_jstfc_disj(v,jstf);
        if (!sign(jstf) && defType[var(jstf)]!=NONDEF && scc[v]==scc[var(jstf)])
            addCycleSource(v);
    } else {
        assert(defType[v]==AGGR);
        bool becomes_cycle_source = false;

        AggrWatch& aw = (Aggr_watches[v])[0];
        vec<AggrSet::WLit>& lits = aw.set->set;
        vec<Lit> nj; // New sp_justification.
        if (aw.set->type==SUM || aw.set->type==PROD) { // Note: no need to test weights, because v is not false.
            for (int i=0; i<lits.size(); ++i) {        // Also note: here we make a huge simplification of possible justifications. It has the advantage of being uniquely defined, and the disadvantage of a higher chance of adding v as a cycle source.
                Lit k = lits[i].lit;
                if (value(k)==l_Undef) {
                    nj.push(k);
                    nj.push(~k);
                    if (!becomes_cycle_source && defType[var(k)]!=NONDEF && scc[v]==scc[var(k)]) // first test: to avoid having to do other tests.
                        becomes_cycle_source=true;
                } else {
                    if (value(k)==l_False) k=~k;
                    nj.push(k);
                    if (!becomes_cycle_source && !sign(k) && defType[var(k)]!=NONDEF && scc[v]==scc[var(k)])
                        becomes_cycle_source=true;
                }
            }
        } else if (aw.set->type==MIN) {
            int i=0; for (; lits[i].weight<aw.expr->min; ++i) { // NOTE: because v is not false, the test will fail before i==set.size(), and also none of the encountered literals will be true.
                Lit k = lits[i].lit;
                nj.push(~k);
                if (!becomes_cycle_source && sign(k) && defType[var(k)]!=NONDEF && scc[v]==scc[var(k)])
                    becomes_cycle_source=true;
            }
            for (; value(lits[i].lit)!=l_False; ++i); // NOTE: because v is not false, the test will fail before i==set.size()
            Lit k = lits[i].lit;
            nj.push(k);
            if (!becomes_cycle_source && !sign(k) && defType[var(k)]!=NONDEF && scc[v]==scc[var(k)])
                becomes_cycle_source=true;
        } else { // MAX
            int i=lits.size()-1; for (; lits[i].weight>aw.expr->max; --i) { // NOTE: because v is not false, the test will fail before i<0, and also none of the encountered literals will be true.
                Lit k = lits[i].lit;
                nj.push(~k);
                if (!becomes_cycle_source && sign(k) && defType[var(k)]!=NONDEF && scc[v]==scc[var(k)])
                    becomes_cycle_source=true;
            }
            for (; value(lits[i].lit)!=l_False; --i); // NOTE: because v is not false, the test will fail before i<0
            Lit k = lits[i].lit;
            nj.push(k);
            if (!becomes_cycle_source && !sign(k) && defType[var(k)]!=NONDEF && scc[v]==scc[var(k)])
                becomes_cycle_source=true;
        }

        change_jstfc_aggr(v,nj);
        if (becomes_cycle_source)
            addCycleSource(v);
    }
}

bool Solver::indirectPropagateNow() {
    if (defn_strategy==always)
        return true;
    // Decide if state is two-valued (then we definitely have to search).
    Var v = var_Undef;
    while (v==var_Undef || toLbool(assigns[v]) != l_Undef || !decision_var[v]) {
        if (v!=var_Undef) order_heap.removeMin();
        if (order_heap.empty()) {
            v = var_Undef;
            break;
        } else
            v = order_heap[0];
    }
    if (v!=var_Undef) {
        if (defn_strategy==lazy) return false;
        if (defn_strategy==adaptive && adaption_current<adaption_total) {
            adaption_current++;
            return false;
        }
    }
    return true;
}

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
Clause* Solver::indirectPropagate() {
    if (!indirectPropagateNow())
        return NULL;
    findCycleSources();

    bool ufs_found=false;
    std::set<Var> ufs;
    int i=0; uint64_t old_justify_calls = justify_calls;
    for (; !ufs_found && i<css.size(); i++)
        if (isCS[css[i]])
            ufs_found = unfounded(css[i], ufs);

    if(verbosity>=2){
    	if(ufs_found){
    		reportf("ufs found, size %i", ufs.size());
    	}
    }

    justifiable_cycle_sources+=ufs_found?(i-1):i; // This includes those that are removed inside "unfounded".
    succesful_justify_calls+=(justify_calls - old_justify_calls);

    if (ufs_found) {
        if (verbosity>=2) {
            reportf("Found an unfounded set of size %d: {",ufs.size());
            for (std::set<Var>::iterator it=ufs.begin();it!=ufs.end();++it) reportf(" %d",*it+1);
            reportf(" }.\n");
        }
        cycles++; cycle_sizes+=ufs.size();
        if (defn_strategy==adaptive) adaption_current++; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
        return assertUnfoundedSet(ufs);
    } else { // Found a witness justification.
        apply_changes();
        if (defn_strategy==adaptive) {
            if (adaption_current==adaption_total)
                adaption_total++; // Next time, skip one decision level extra.
            else
                adaption_total--;
            if (adaption_total<0) adaption_total=0;
            adaption_current=0;
        }
        // fwIndirectPropagate();
        // NB: nb of witnesses found == nb of decisions made in case of "always"
        //if (verbosity>=2) assert(isCycleFree()); // Only debugging! Time consuming.
        return NULL;
    }
}

bool Solver::unfounded(Var cs, std::set<Var>& ufs) {
    justify_calls++;
    bool rslt=false;  // if we go straight to Finish, this will be the result.
    vec<Var> tmpseen; // use to speed up the cleaning of data structures in "Finish"
    Queue<Var> q;
    Var v;
    markNonJustified(cs, tmpseen);
    if (!seen[cs]) {isCS[cs] = false; goto Finish;} // 'seen[v]' means: v has path to cs in current sp_justification.

    q.insert(cs);
    ufs.clear();
    ufs.insert(cs);

    while (q.size() > 0) {
        v = q.peek(); q.pop();
        if (!seen[v]) continue;
        if (directlyJustifiable(v,ufs,q))
            if (Justify(v,cs,ufs,q)) goto Finish;
    }
    assert(ufs.size() > 0); // The ufs atoms form an unfounded set. 'cs' is in it.
    rslt = true;
Finish:
    for (int i=0;i<tmpseen.size();i++) { seen[tmpseen[i]]=0; /*used_conj[tmpseen[i]].clear(); WITH guards system*/ }
    return rslt;
}

// Helper for 'unfounded(..)'. True if v can be immediately justified by one change_justification action.
bool Solver::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q) {
    switch(defType[v]) {
        case CONJ:{
            Clause& c = *definition[v]; // NOTE: sign(c[i]) fails for the head literal; for body literals sign is inverted.
            // Find a non-justified body literal, pref. already ufs.
            // - If not found: bottom up propagation
            // - If found: set conjunction's watch to it; make sure it's ufs and on queue.
            int i=0; for (; i<c.size() && !(sign(c[i]) && seen[var(c[i])]); ++i);
            if (i==c.size()) return true; // Each body literal has either !sign (is negative) or !seen (is justified wrt v).

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
            for (; i<c.size(); ++i) {
                Var x = var(c[i]);
                if (seen[x] && sign(c[i])) {
                    seen[v]++;
                    std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(x);
                    if (pr.second)
                        q.insert(x);
                }
            }
            break;}
        case DISJ:{
            Clause& c = *definition[v];
            // Find a justified non-false body literal.
            // - If found: set watch to it; bottom up propagation
            // - If not found: touch all non-false body literals; add them to queue.
            vec<Var> add_to_q;
            for (int i=0; i<c.size(); ++i) {
                Lit bdl = c[i]; Var b = var(bdl);
                if (bdl != Lit(v,true) && value(bdl) != l_False) {
                    if (sign(bdl) || !seen[b]) {
                        change_jstfc_disj(v, bdl);
                        return true; // bad style, but anyway...
                    } else
                        add_to_q.push(b);
                }
            }
            for (int i=0; i<add_to_q.size(); ++i) {
                std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(add_to_q[i]);
                if (pr.second)
                    q.insert(add_to_q[i]);
            }
            break;}
        case AGGR:{
            AggrWatch& aw = (Aggr_watches[v])[0];
            vec<AggrSet::WLit>& lits = aw.set->set;
            switch (aw.set->type) {
                case SUM:{
                    int min=0; int max=aw.set->cmax;
                    bool complete=false;
                    vec<Lit> nj; vec<Var> add_to_q;
                    // Use only negative or justified literals.
                    for (int i=0; !complete && i<lits.size(); ++i) {
                        Lit l = lits[i].lit;
                        // Note: l_Undef literals may be used twice, once pos and once neg!
                        if (value(l)!=l_False) {
                            if (!sign(l) && seen[var(l)]) {
                                if (ufs.find(var(l)) == ufs.end())
                                    add_to_q.push(var(l));
                            } else {
                                nj.push(l);
                                min+=lits[i].weight;
                                if (min>=aw.expr->min && max<=aw.expr->max) complete=true;
                            }
                        }
                        if (value(l)!=l_True) {
                            if (sign(l) && seen[var(l)]) {
                                if (ufs.find(var(l)) == ufs.end())
                                    add_to_q.push(var(l));
                            } else {
                                nj.push(~l);
                                max-=lits[i].weight;
                                if (min>=aw.expr->min && max<=aw.expr->max) complete=true;
                            }
                        }
                    }
                    if (complete) {
                        change_jstfc_aggr(v,nj);
                        return true;
                    } else {
                        for (int i=0; i<add_to_q.size(); ++i) {
                            q.insert(add_to_q[i]);
                            ufs.insert(add_to_q[i]);
                        }
                    }
                    break;}
                case PROD:{
                    int min=1; int max=aw.set->cmax;
                    bool complete=false;
                    vec<Lit> nj; vec<Var> add_to_q;
                    // Use only negative or justified literals.
                    for (int i=0; !complete && i<lits.size(); ++i) {
                        Lit l = lits[i].lit;
                        if (value(l)!=l_False) {
                            if (!sign(l) && seen[var(l)]) {
                                if (ufs.find(var(l)) == ufs.end())
                                    add_to_q.push(var(l));
                            } else {
                                nj.push(l);
                                min*=lits[i].weight;
                                if (min>=aw.expr->min && max<=aw.expr->max) complete=true;
                            }
                        }
                        if (value(l)!=l_True) {
                            if (sign(l) && seen[var(l)]) {
                                if (ufs.find(var(l)) == ufs.end())
                                    add_to_q.push(var(l));
                            } else {
                                nj.push(~l);
                                max=max/lits[i].weight;
                                if (min>=aw.expr->min && max<=aw.expr->max) complete=true;
                            }
                        }
                    }
                    if (complete) {
                        change_jstfc_aggr(v,nj);
                        return true;
                    } else {
                        for (int i=0; i<add_to_q.size(); ++i) {
                            q.insert(add_to_q[i]);
                            ufs.insert(add_to_q[i]);
                        }
                    }
                    break;}
                case MIN:{
                    vec<Var> add_to_q; vec<Lit> nj;
                    int i=0; for (; lits[i].weight<aw.expr->min; ++i) { // NOTE: these are exactly the same always. Find some way of doing this only the first time.
                        Lit l = lits[i].lit;
                        nj.push(~l);
                        if (sign(l) && seen[var(l)] && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end())
                            add_to_q.push(var(l));
                    }
                    int atqsize = add_to_q.size();
                    for (; lits[i].weight<=aw.expr->max; ++i) {
                        Lit l = lits[i].lit;
                        if (value(l)!=l_False) {
                            if (!sign(l) && seen[var(l)] && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end())
                                add_to_q.push(var(l));
                            else {
                                nj.push(l);
                                break;
                            }
                        }
                    }
                    if (lits[i].weight<aw.expr->min) {
                        if (atqsize==0) {
                            change_jstfc_aggr(v,nj);
                            return true;
                        }
                    } else
                        atqsize = add_to_q.size();
                    for (int i=0; i<atqsize; ++i) {
                        q.insert(add_to_q[i]);
                        ufs.insert(add_to_q[i]);
                    }
                    break;}
                case MAX:{
                    vec<Var> add_to_q; vec<Lit> nj;
                    int i=lits.size()-1; for (; lits[i].weight>aw.expr->max; --i) { // NOTE: these are exactly the same always. Find some way of doing this only the first time.
                        Lit l = lits[i].lit;
                        nj.push(~l);
                        if (sign(l) && seen[var(l)] && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end())
                            add_to_q.push(var(l));
                    }
                    int atqsize = add_to_q.size();
                    for (; lits[i].weight>=aw.expr->min; --i) {
                        Lit l = lits[i].lit;
                        if (value(l)!=l_False) {
                            if (!sign(l) && seen[var(l)] && scc[v]==scc[var(l)] && ufs.find(var(l)) == ufs.end())
                                add_to_q.push(var(l));
                            else {
                                nj.push(l);
                                break;
                            }
                        }
                    }
                    if (lits[i].weight<aw.expr->min) {
                        if (atqsize==0) {
                            change_jstfc_aggr(v,nj);
                            return true;
                        }
                    } else
                        atqsize = add_to_q.size();
                    for (int i=0; i<atqsize; ++i) {
                        q.insert(add_to_q[i]);
                        ufs.insert(add_to_q[i]);
                    }
                    break;}
            }
            break;}
        default:
            assert(false);
    }

    return false;
}

// Helper for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified.
bool Solver::Justify(Var v, Var cs, std::set<Var>& ufs, Queue<Var>& q) {
    Queue<Var> tojustify; tojustify.insert(v); // ... starting with v.
    while (tojustify.size() > 0) {
        Var k = tojustify.peek(); tojustify.pop();
        if (seen[k]) { // Prevent infinite loop. NB: 'seen' here is the same as in 'unfounded': means: k has path in sp_justification to cs.
            // Make it justified.
            ufs.erase(k);
            seen[k] = 0;
            if (isCS[k]) {isCS[k] = false; cs_removed_in_justify++;}
            if (k == cs) return true;

            // Record also disjunctions that now become justified for bottom-up propagation.
            vec<Var>& disjs = disj_occurs[k+k]; // k+k is the index of the positive literal k.
            for (int i=0; i<disjs.size(); ++i) {
                Var d = disjs[i];
                if (seen[d]) {                            // && ufs.find(d) != ufs.end()) //   WITH this extra test: only bottom-up propagate in already marked literals.
                    change_jstfc_disj(d,Lit(k,false));
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
            vec<Var>& conjs = conj_occurs[k+k];
            for (int i=0; i<conjs.size(); ++i) {
                Var c = conjs[i];
                if (seen[c] && ufs.find(conjs[i]) != ufs.end()) { //  NOTE: we use 'seen' as a counter, but the counter is set *only* for literals in ufs. So the extra test is required here.
                    if (seen[c]==1)
                        tojustify.insert(c); // Recall that the if-test in the beginning checks whether the atom is 'seen'.
                    else
                        seen[c]--;
                }
            }

            if (ecnf_mode.aggr) {
                // Record aggregates that might now be justified on the main queue. TODO : can we do this less eagerly? something like used_conjs?
                vec<AggrWatch>& aw = Aggr_watches[k];
                for (int i=0; i<aw.size(); ++i) {
                    if (aw[i].type==DEFN) continue;
                    vec<AggrExpr*>& exprs = aw[i].set->exprs;
                    for (int j=0; j<exprs.size(); ++j) {
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
void Solver::change_jstfc_disj(Var v, Lit j) {
    assert(defType[v]==DISJ);
    sp_justification_disj[v]=j;
    changed_vars.push(v);
}

// Change sp_justification: v is now justified by j.
void Solver::change_jstfc_aggr(Var v, const vec<Lit>& j) {
    // NOTE: maybe more efficient implementation possible if j changes very little from previous justification? Especially for MIN and MAX.
    assert(defType[v]==AGGR);
    sp_justification_aggr[v].clear();
    for (int i=0; i<j.size(); i++) sp_justification_aggr[v].push(j[i]);
    changed_vars.push(v);
}

/* If an atom of 'ufs' was already true, return a loop formula for this (one
 * such) atom as conflicting clause.
 * Otherwise, add a loop formula for each atom in ufs, enqueue the negation of
 * each of those atoms, and return NULL.
 */
Clause* Solver::assertUnfoundedSet(const std::set<Var>& ufs) {

    assert(!ufs.empty());
    // Create the loop formula: add the antecedents (first element will be filled in later).
    vec<Lit> loopf(1);
    for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
        switch (defType[*tch]) {
            case CONJ:{
                break;}
            case DISJ:{
                Clause& cl = *definition[*tch];
                for (int i=0; i<cl.size(); i++) {
                    Lit l = cl[i];
                    if (l != Lit(*tch,true) && seen[var(l)]!=(sign(l)?1:2) && ufs.find(var(cl[i])) == ufs.end()) {
                        loopf.push(l);
                        seen[var(l)]=(sign(l)?1:2); // Just in case P and ~P both appear; otherwise we might get something between well-founded and ultimate semantics...
                    }
                }
                break;}
            case AGGR:{
                AggrWatch& aw = (Aggr_watches[*tch])[0];
                vec<AggrSet::WLit>& lits = aw.set->set;
                if (aw.set->type==SUM || aw.set->type==PROD) {
                    for (int i=0; i<lits.size(); ++i) {
                        Lit l = lits[i].lit;
                        if (value(l)==l_True) {
                            if (sign(l) || ufs.find(var(l))==ufs.end()) {
                                loopf.push(l);
                                seen[var(l)]=(sign(l)?1:2);
                            }
                        } else if (value(l)==l_False) {
                            if (~sign(l) || ufs.find(var(l))==ufs.end()) {
                                loopf.push(~l);
                                seen[var(l)]=(sign(l)?2:1);
                            }
                        }
                    }
                } else if (aw.set->type==MIN) {
                        int i=0; for (; lits[i].weight<aw.expr->min; ++i) {
                            if (ufs.find(var(lits[i].lit)) == ufs.end()) {
                                loopf.push(~lits[i].lit);
                                seen[var(lits[i].lit)]=(sign(lits[i].lit)?2:1);
                            }
                        }
                        for (; lits[i].weight<=aw.expr->max; ++i) {
                            if (ufs.find(var(lits[i].lit)) == ufs.end()) {
                                loopf.push(lits[i].lit);
                                seen[var(lits[i].lit)]=(sign(lits[i].lit)?1:2);
                            }
                        }
                } else { // MAX
                    int i=lits.size()-1; for (; lits[i].weight>aw.expr->max; --i) {
                        if (ufs.find(var(lits[i].lit)) == ufs.end()) {
                            loopf.push(~lits[i].lit);
                            seen[var(lits[i].lit)]=(sign(lits[i].lit)?2:1);
                        }
                    }
                    for (; lits[i].weight>=aw.expr->min; --i) {
                        if (ufs.find(var(lits[i].lit)) == ufs.end()) {
                            loopf.push(lits[i].lit);
                            seen[var(lits[i].lit)]=(sign(lits[i].lit)?1:2);
                        }
                    }
                }
                break;}
        }
    }
    for (int i=1;i<loopf.size();i++) seen[var(loopf[i])]=0;
    extdisj_sizes+=loopf.size()-1;

    if (defn_strategy!=always) {// Maybe the loop formula could have been derived at an earlier level: in that case we first have to backtrack to that level.
        // Set the backtrack level.
        int lvl=0;
        for (int i=1;i<loopf.size();i++)
            if (level[var(loopf[i])]>lvl) lvl=level[var(loopf[i])];
        cancelUntil(lvl);
    }

    // Verify whether a conflict ensues.
    for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
        Var v = *tch;
        if (value(v)==l_True) {
            loopf[0] = Lit(v,true);
            Clause* c = Clause_new(loopf, true);
            learnts.push(c); attachClause(*c); claBumpActivity(*c);
            if (verbosity>=2) {reportf("Adding conflicting loop formula: [ "); printClause(*c); reportf("].\n");}
            justify_conflicts++;
            return c;
        }
    }

    // No conflict: then enqueue all facts and their loop formulas.
    if (loopf.size() >= 5) { // Then we introduce a new variable for the antecedent part.
        Var v = newVar();
        if (verbosity>=2) {reportf("Adding new variable for loop formulas: %d.\n",v+1);}
        // v \equiv \bigvee\extdisj{L}
        // ~v \vee \bigvee\extdisj{L}.
        loopf[0] = Lit(v,true); Clause* c = Clause_new(loopf, true);
        learnts.push(c); attachClause(*c); claBumpActivity(*c);
        if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        uncheckedEnqueue(loopf[0], c);
        // \bigwedge_{d\in\extdisj{L}} v \vee ~d.
        vec<Lit> binaryclause(2); binaryclause[0] = Lit(v,false);
        for (int i=1; i<loopf.size(); ++i) {
            binaryclause[1] = ~loopf[i];
            Clause* c = Clause_new(binaryclause, true);
            learnts.push(c); attachClause(*c); claBumpActivity(*c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }

        // \bigwedge_{l\in L} \neg l \vee v
        binaryclause[1] = Lit(v,false);
        for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
            binaryclause[0] = Lit(*tch,true); Clause* c = Clause_new(binaryclause, true);
            learnts.push(c); attachClause(*c); claBumpActivity(*c);
            //uncheckedEnqueue(binaryclause[0], c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }
    } else { // We simply add the loop formula as is.
        for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
            loopf[0] = Lit(*tch,true); Clause* c = Clause_new(loopf, true);
            learnts.push(c); attachClause(*c); claBumpActivity(*c);
            uncheckedEnqueue(loopf[0], c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }
    }
    return NULL;
}

/* Precondition:  !seen[i] for each i.
 * Postcondition: seen[i]  for exactly those i that are ancestors of cs in sp_justification. If defn_search==stop_at_cs, there should not be other cycle sources then cs in the path from added literals to cs.
 */
void Solver::markNonJustified(Var cs, vec<Var>& tmpseen) {

    Queue<Var> q;
    markNonJustifiedAddParents(cs,cs,q,tmpseen);
    // Now recursively do the same with each enqueued Var.
    Var x;
    while (q.size() > 0) {
        x = q.peek(); q.pop();
        markNonJustifiedAddParents(x,cs,q,tmpseen);
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

void Solver::markNonJustifiedAddVar(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
    if (!seen[v] && (scc[v]==scc[cs]) && (defn_search==include_cs || v==cs || !isCS[v])) {
        seen[v]=1;
        tmpseen.push(v);
        q.insert(v);
        total_marked_size++;
    }
}

void Solver::markNonJustifiedAddParents(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
    vec<Var>& v = disj_occurs[x+x];
    for (int i=0; i<v.size(); ++i)
        if (var(sp_justification_disj[v[i]])==x)
            markNonJustifiedAddVar(v[i],cs,q,tmpseen);
    vec<Var>& w = conj_occurs[x+x];
    for (int i=0; i<w.size(); i++)
        markNonJustifiedAddVar(w[i],cs,q,tmpseen);

    if (ecnf_mode.aggr) {
        vec<AggrWatch>& aw = Aggr_watches[x];
        for (int i=0; i<aw.size(); i++) {
            if (aw[i].type!=DEFN) { // Else x is the head, hence not used in the justification.
                for (int j=0; j<aw[i].set->exprs.size(); j++) {
                    Var y=var(aw[i].set->exprs[j]->c); // Find the head of the aggregate expression where x is watched in the body.
                    vec<Lit>& jstfc = sp_justification_aggr[y];
                    int k=0; for (; k<jstfc.size() && jstfc[k]!=Lit(x,false); k++); 
                    if (k<jstfc.size()) // Found that x is actually used in y's justification.
                        markNonJustifiedAddVar(y,cs,q,tmpseen);
                }
            }
        }
    }
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (toLbool(assigns[next]) == l_Undef && decision_var[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_user:  sign = polarity[next]; break;
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    default: assert(false); }

    return next == var_Undef ? lit_Undef : Lit(next, sign);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|  
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    bool deleteImplicitClause=false;
    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level[var(q)] > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level[var(q)] >= decisionLevel())
                    pathC++;
                else{
                    out_learnt.push(q);
                    if (level[var(q)] > out_btlevel)
                        out_btlevel = level[var(q)];
                }
            }
        }

        if (deleteImplicitClause) {
            delete confl;
            deleteImplicitClause = false;
        }
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason[var(p)];
        if (confl==NULL && pathC>1) {
            confl=implicitReasonClause(p);
            deleteImplicitClause = true;
        }
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    if (expensive_ccmin){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[var(out_learnt[i])] == NULL || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
    }else{
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++){
            Clause& c = *reason[var(out_learnt[i])];
            for (int k = 1; k < c.size(); k++)
                if (!seen[var(c[k])] && level[var(c[k])] > 0){
                    out_learnt[j++] = out_learnt[i];
                    break; }
        }
    }
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        for (int i = 2; i < out_learnt.size(); i++)
            if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
                max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level[var(p)];
    }


    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level[var(p)] > 0){
                if (reason[var(p)] != NULL && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason[x] == NULL){
                assert(level[x] > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = *reason[x];
                for (int j = 1; j < c.size(); j++)
                    if (level[var(c[j])] > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}

Clause* Solver::aggrEnqueue(Lit p, AggrReason* ar)
{ 
    if (verbosity>=2) {
        reportf("%seriving ", value(p)==l_True ? "Again d" : "D");
        printLit(p);
        reportf(" because of the aggregate expression ");
        printAggrExpr(*ar->expr,*ar->set);
    }

    if (value(p) == l_False) {
        if (verbosity>=2) reportf("Conflict.\n");
        AggrReason* old_ar=aggr_reason[var(p)];
        aggr_reason[var(p)]=ar;
        Clause* confl = implicitReasonClause(p);
        learnts.push(confl); attachClause(*confl); claBumpActivity(*confl);
        aggr_reason[var(p)]=old_ar;
        return confl;
    } else if (value(p)==l_Undef) {
        assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
        level   [var(p)] = decisionLevel();
        reason  [var(p)] = NULL;                    // implicitReasonClause is not necessarily needed, so spend no effert on it yet.
        aggr_reason[var(p)] = ar;
        trail.push(p);
    } else
        delete ar;
    return NULL;
}

void Solver::uncheckedEnqueue(Lit p, Clause* from)
{
    assert(value(p) == l_Undef);
    assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
    level   [var(p)] = decisionLevel();
    reason  [var(p)] = from;
    trail.push(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause* Solver::propagate()
{
    Clause* confl     = NULL;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Clause*>&  ws  = watches[toInt(p)];
        Clause         **i, **j, **end;
        num_props++;

        if (verbosity>=2) {reportf("Propagating literal "); printLit(p); reportf(": (");}

        for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
            Clause& c = **i++;

            // Make sure the false literal is data[1]:
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            if (value(first) == l_True){
                *j++ = &c;
            }else{
                // Look for new watch:
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[toInt(~c[1])].push(&c);
                        goto FoundWatch; }

                        // Did not find watch -- clause is unit under assignment:
                        *j++ = &c;
                        if (value(first) == l_False){
                            if (verbosity>=2) reportf(" Conflict");
                            confl = &c;
                            qhead = trail.size();
                            // Copy the remaining watches:
                            while (i < end)
                                *j++ = *i++;
                        }else {
                            uncheckedEnqueue(first, &c);
                            if (verbosity>=2) {reportf(" "); printLit(first);}
                        }
            }
FoundWatch:;
        }
        ws.shrink(i - j);
        if (verbosity>=2) reportf(" ).\n");

        // AMO propagations.
        if (confl==NULL && ecnf_mode.amo)
            confl = AMO_propagate(p);

        if (!ecnf_mode.init) { // finishECNF_DataStructures() needs to be executed first.
            // Aggr propagations.
            if (confl==NULL && ecnf_mode.aggr)
                confl = Aggr_propagate(p);

            // Def propagations.
            if (qhead==trail.size()/*Only after all other propagations finished.*/ && confl == NULL && ecnf_mode.def)
                confl = indirectPropagate();

            // TODO TODO: fast way of stopping the while loop if confl != NULL ?
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

Clause* Solver::AMO_propagate(Lit p) {// TODO: if part of an EU statement, change watches there.
    vec<Clause*>& ws = AMO_watches[toInt(p)];
    if (verbosity>=2 && ws.size()>0) {reportf("AMO-propagating literal "); printLit(p); reportf(": (");}
    for (int i=0; i<ws.size(); i++) {
        Clause& c = *ws[i];
        vec<Lit> ps(2); ps[1]=~p;
        for (int j=0; j<c.size(); j++) {
            if (c[j]==p || value(c[j])==l_False)
                continue;
            ps[0]=~c[j]; Clause* rc = Clause_new(ps, true); learnts.push(rc); attachClause(*rc); claBumpActivity(*rc);
            if (value(c[j])==l_True) {
                if (verbosity>=2) reportf(" Conflict");
                qhead = trail.size();
                return rc;
            } else {// (value(c[j])==l_Undef) holds
                uncheckedEnqueue(~c[j], rc);
                if (verbosity>=2) {reportf(" "); printLit(c[j]);}
            }
        }
    }
    if (verbosity>=2 && ws.size()>0) reportf(" ).\n");

    return NULL;
}

void Solver::addSet(int set_id, vec<Lit>& lits, vec<int>& weights) {
    if (!ecnf_mode.aggr)
        reportf("ERROR! Attempt at adding aggregate set, though ECNF specifiers did not contain \"aggr\".\n"), exit(3);
    if (lits.size()==0) { reportf("Error: Set nr. %d is empty,\n",set_id); exit(3); }
    assert(lits.size()==weights.size());
    // Find out if lits contains any doubles.
    vec<Lit> ps(lits.size());
    for (int i=0;i<lits.size(); i++) ps[i]=lits[i];
    sort(ps);
    Lit p; int i;
    for (i = 0, p = lit_Undef; i < ps.size(); i++)
        if (ps[i] == p || ps[i] == ~p)
            reportf("ERROR! (W)Set %d contains the same literal twice.\n",set_id), exit(3);
        else
            p = ps[i];
    // For each set_id we add NB_AGGR_TYPES sets.
    while (set_id*NB_AGGR_TYPES > aggr_sets.size()) aggr_sets.push(new AggrSet()); // NOTE: each of these has type "SUM"!
    // But we only initialize the default one.
    AggrSet &as = *aggr_sets[(set_id-1)*NB_AGGR_TYPES+SUM];
    if (as.set.size() > 0) { reportf("Error: Set nr. %d is defined more then once.\n",set_id), exit(3); }
    for (int i=0;i<lits.size();i++) {
        if (weights[i]<0) { reportf("Error: Set nr. %d contains a negative weight, %d.\n",set_id,weights[i]), exit(3); }
        as.set.push(AggrSet::WLit(lits[i],weights[i]));
        as.max += weights[i];
    }
    qsort(as.set, as.set.size(), sizeof(AggrSet::WLit), compare_WLits);
    as.cmax=as.max;
}

void Solver::Subsetminimize(const vec<Lit>& lits) {
    if (!ecnf_mode.mnmz)
        reportf("ERROR! Attempt at adding a subset minimize statement, though ECNF specifiers did not contain \"mnmz\".\n"), exit(3);
    if (lits.size()==0) { reportf("Error: The set of literals to be minimized is empty,\n"); exit(3); }
    if (to_minimize.size()!=0) { reportf("At most one set of literals to be minimized can be given.\n"); exit(3); }

    for (int i=0;i<lits.size();i++)
        to_minimize.push(lits[i]);
}

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
void Solver::addAggrExpr(int defn, int set_id, int min, int max, AggrType type) {
    if (!ecnf_mode.aggr)
        reportf("ERROR! Attempt at adding aggregate expression, though ECNF specifiers did not contain \"aggr\".\n"), exit(3);

    if (set_id*NB_AGGR_TYPES>aggr_sets.size()) {reportf("Error: Set nr. %d is used, but not defined yet.\n",set_id), exit(3);}
    if (min<0 || min>max) {reportf("Error: aggregate expression with minimum %d and maximum %d is not valid.\n",min,max), exit(3);}

    Lit c = Lit(defn,false);
    defType[var(c)]=AGGR;
    varBumpActivity(var(c)); // These guys ought to be initially a bit more important then the rest.
    if (ecnf_mode.def)
        defdVars.push(var(c));
    AggrExpr* ae = new AggrExpr(min,max,c);
    aggr_exprs.push(ae);
    AggrSet* as = aggr_sets[(set_id-1)*NB_AGGR_TYPES+type];
    as->exprs.push(ae);
    if (as->type==SUM && type!=SUM) {
        // It's the first aggregate expression of type 'type' for this set. Initialize the set.
        as->type=type;
        AggrSet* sum_as = aggr_sets[(set_id-1)*NB_AGGR_TYPES+SUM]; // We'll copy from this set, which has been initialized already.
        for (int i=0;i<sum_as->set.size();i++)
            as->set.push(sum_as->set[i]);
        switch (as->type) {
            // If type=SUM or PROD: min/max  attainable with current truth values. If type=MIN: index of first non-false / first true literal (can go out of range!); if type=MAX: index of last true / last non-false literal (can go out of range!).
            case PROD:
                as->min = 1;
                as->max = 1;
                for (int i=0;i<sum_as->set.size();i++)
                    as->max *= sum_as->set[i].weight;
                as->cmax=as->max;
                if (as->cmax==0)
                    reportf("ERROR! Weight zero in a PROD expression.\n"), exit(3);
                break;
            case MIN:
                as->min = 0;                // [,)
                as->max = as->set.size();   // [,)
                break;
            case MAX:
                as->min = -1;               // (,]
                as->max = as->set.size()-1; // (,]
                break;
            default:
                assert(false);
                break;
        }
    }

    Aggr_watches[var(c)].push(AggrWatch(as,ae,-1,DEFN));

    bool already_occurs=false; // Making sure that for a set with several expressions, watches from the set literals are added only once.
    vec<AggrWatch>& vcw = Aggr_watches[var(as->set[0].lit)]; // Note: set is not empty.
    for (int i=0; !already_occurs && i<vcw.size(); i++)
        if (vcw[i].set == as)
            already_occurs=true;
    for (int i=0; !already_occurs && i<as->set.size(); i++)
        Aggr_watches[var(as->set[i].lit)].push(AggrWatch(as,NULL,i,sign(as->set[i].lit)?NEG:POS));
}

Clause* Solver::Aggr_propagate(Lit p) { // TODO: do something about double work? E.g. first propagation head->some body literal, then backward again...
    Clause* confl=NULL;

    vec<AggrWatch>& ws = Aggr_watches[var(p)];
    if (verbosity>=2 && ws.size()>0) reportf("Aggr_propagate(%s%d).\n",sign(p)?"-":"",var(p)+1);
    for (int i=0; confl==NULL && i<ws.size(); i++){
        AggrSet& as=*ws[i].set;
        Occurrence tp = relativeOccurrence(ws[i].type,p);
        as.stack.push(AggrSet::PropagationInfo(p, as.set[ws[i].index].weight, tp));
        if (tp==DEFN) // It's a defining literal.
            confl = Aggr_propagate(as,*ws[i].expr);
        else {                   // It's a set literal.
            // First update the set's "min" and "max" values.
            bool trues = tp==POS;
            switch (as.type) {
                case SUM:
                    if (trues) as.min+=as.set[ws[i].index].weight;
                    else       as.max-=as.set[ws[i].index].weight;
                    break;
                case PROD:
                    // NOTE: this assumes weights are different from zero!
                    if (trues) as.min*=as.set[ws[i].index].weight;
                    else       {assert(as.max % as.set[ws[i].index].weight==0); as.max=as.max / as.set[ws[i].index].weight;}
                    break;
                case MIN:
                    if (trues) {if (ws[i].index<as.max) as.max=ws[i].index;}
                    else       {/*if (ws[i].index==as.min)*/ while(as.min<as.set.size() && value(as.set[as.min].lit)==l_False) ++as.min;}
                    break;
                case MAX:
                    if (trues) {if (ws[i].index>as.min) as.min=ws[i].index;}
                    else       {/*if (ws[i].index==as.max)*/ while(as.max>=0 && value(as.set[as.max].lit)==l_False) --as.max;}
                    break;
                default:
                    assert(false);
                    break;
            }
            int min=as.min; int max=as.max;

            if (as.type==MIN) {
                if (as.min<as.set.size()) min=as.set[as.min].weight; else min=2147483647;
                if (as.max<as.set.size()) max=as.set[as.max].weight; else max=2147483647;
            } else if (as.type==MAX) {
                if (as.min>=0) min=as.set[as.min].weight; else min=-1;
                if (as.max>=0) max=as.set[as.max].weight; else max=-1;
            }
            // Now try to propagate.
            for (int e=0; confl==NULL && e<as.exprs.size(); e++) {
                AggrExpr& ae=*as.exprs[e];
                if (min>=ae.min && max<=ae.max)
                    confl = aggrEnqueue(ae.c,new AggrReason(&ae,&as,DEFN));
                else if (min>ae.max)
                    confl = aggrEnqueue(~ae.c,new AggrReason(&ae,&as,DEFN));
                else if (max<ae.min)
                    confl = aggrEnqueue(~ae.c,new AggrReason(&ae,&as,DEFN));
                else
                    confl = Aggr_propagate(as,ae);
            }
        }
    }

    return confl;
}

Clause* Solver::Aggr_propagate(AggrSet& as, AggrExpr& ae) {
    Clause* confl=NULL;
    switch (as.type) {
        // TODO SUM / PROD propagations can be made more efficient using ordering of literals!!
        case SUM:
            if (value(ae.c)==l_True) {
                for (int u=0;u<as.set.size();u++) {
                    if (value(as.set[u].lit)==l_Undef) {// no conflict possible
                        if (as.min+as.set[u].weight>ae.max)
                            aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
                        else if (as.max-as.set[u].weight<ae.min)
                            aggrEnqueue(as.set[u].lit,new AggrReason(&ae,&as,POS));
                    }
                }
            } else if (value(ae.c)==l_False) {
                if (as.min>=ae.min || as.max<=ae.max) {// no conflicts possible
                    int minw=2147483647;
                    for (int u=0;u<as.set.size();u++)
                        if (value(as.set[u].lit)==l_Undef && as.set[u].weight<minw)
                            minw=as.set[u].weight;
                    bool maketrue  = minw!=2147483647 && as.min>=ae.min && as.max-minw<=ae.max;
                    bool makefalse = minw!=2147483647 && as.max<=ae.max && as.min+minw>=ae.min;
                    if (maketrue)
                        for (int u=0;u<as.set.size();u++)
                            if (value(as.set[u].lit)==l_Undef)
                                aggrEnqueue(as.set[u].lit,new AggrReason(&ae,&as,POS));
                    if (makefalse)
                        for (int u=0;u<as.set.size();u++)
                            if (value(as.set[u].lit)==l_Undef)
                                aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
                }
            }
            break;
        case PROD: // cfr. SUM, but * and / instead of + and -.
            if (value(ae.c)==l_True) {
                for (int u=0;u<as.set.size();u++) {
                    if (value(as.set[u].lit)==l_Undef) {
                        if (as.min*as.set[u].weight>ae.max)
                            aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
                        else if (as.max/as.set[u].weight<ae.min)
                            aggrEnqueue(as.set[u].lit,new AggrReason(&ae,&as,POS));
                    }
                }
            } else  if (value(ae.c)==l_False) {
                if (as.min>=ae.min || as.max<=ae.max) {
                    int minw=2147483647;
                    for (int u=0;u<as.set.size();u++)
                        if (value(as.set[u].lit)==l_Undef && as.set[u].weight<minw)
                            minw=as.set[u].weight;
                    bool maketrue  = minw!=2147483647 && as.min>=ae.min && as.max/minw<=ae.max;
                    bool makefalse = minw!=2147483647 && as.max<=ae.max && as.min*minw>=ae.min;
                    if (maketrue)
                        for (int u=0;u<as.set.size();u++)
                            if (value(as.set[u].lit)==l_Undef)
                                aggrEnqueue(as.set[u].lit,new AggrReason(&ae,&as,POS));
                    if (makefalse)
                        for (int u=0;u<as.set.size();u++)
                            if (value(as.set[u].lit)==l_Undef)
                                aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
                }
            }
            break;
        case MIN:
            if (value(ae.c)==l_True) {
                for (int u=as.min; confl==NULL && u<as.set.size() && as.set[u].weight<ae.min; ++u)
                    confl = aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
            } else  if (value(ae.c)==l_False) {
                if (as.min<as.set.size() && as.set[as.min].weight>=ae.min)
                    for (int u=as.min; confl==NULL && u<as.set.size() && as.set[u].weight<=ae.max; ++u)
                        confl = aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
            }
            break;
        case MAX:
            if (value(ae.c)==l_True) {
                for (int u=as.max; confl==NULL && u>=0 && as.set[u].weight>ae.max; --u)
                    confl = aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
            } else  if (value(ae.c)==l_False) {
                if (as.max>=0 && as.set[as.max].weight<=ae.max)
                    for (int u=as.max; confl==NULL && u>=0 && as.set[u].weight>=ae.min; --u)
                        confl = aggrEnqueue(~as.set[u].lit,new AggrReason(&ae,&as,NEG));
            }
            break;
        default:
            assert(false);
            break;
    }
    return confl;
}
/* TODO (@&) if there is but one remaining non-false literal with weight <= ae.max, that literal has to be made true.
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

 TODO as.set[as.max].weight <= ae.max and there is but one non-false literal with weight < ae.min, that literal has to become true.
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

 TODO if there is but one remaining non-false literal with weight >= ae.min, that literal has to be made true.
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

 TODO as.set[as.max].weight <= ae.max and there is but one non-false literal with weight < ae.min, that literal has to become true.
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

Clause* Solver::implicitReasonClause(Lit p) {
    assert(ecnf_mode.aggr);
    vec<Lit> lits;
    lits.push(p);

    AggrReason& ar = *aggr_reason[var(p)];
    int i=0; for (; i<Aggr_watches[var(p)].size() && (Aggr_watches[var(p)])[i].set!=ar.set; ++i); assert(i<Aggr_watches[var(p)].size()); int p_idx=(Aggr_watches[var(p)])[i].index;
    AggrType tp = ar.set->type;
    if (tp == SUM || tp == PROD) {
        int cmax=ar.set->cmax;
        int min_needed=tp==SUM?0:1; int max_needed=cmax;
        if (ar.type==DEFN) {
            // [mn >= i && mx =< j  ==>  c]  OR  [mn > j  || mx < i  ==>  ~c]
            if (ar.expr->c==p) {
                min_needed = ar.expr->min;
                max_needed = ar.expr->max;
            } else {
                assert(ar.expr->c==~p);
                if (ar.set->min > ar.expr->max)
                    min_needed = ar.expr->max+1;
                else
                    max_needed = ar.expr->min-1;
            }
        } else if (ar.type==POS) {
            // c is true && mx = i  OR  c is false && mn >= i && mx = j+1
            if (value(ar.expr->c)==l_True) {
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
            if (value(ar.expr->c)==l_True) {
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
        Lit q; char t;
        for (int i=0; min_needed + (cmax - max_needed) > (ar.set->type==SUM?0:1); i++) {
            q=ar.set->stack[i].lit;
            assert(q!=p); // We should have assembled a reason clause before encountering this.
            t=ar.set->stack[i].type;

            // if (t==0) then q is irrelevant to this derivation.
            if (t==1 && min_needed>(ar.set->type==SUM?0:1)) {
                lits.push(~q);
                if (ar.set->type==SUM)
                    min_needed -= ar.set->stack[i].weight;
                else /*PROD*/
                    min_needed = min_needed / ar.set->stack[i].weight + (min_needed%ar.set->stack[i].weight==0 ? 0:1);
            } else if (t==2 && max_needed<cmax) {
                lits.push(~q);
                if (ar.set->type==SUM)
                    max_needed += ar.set->stack[i].weight;
                else /*PROD*/
                    max_needed *= ar.set->stack[i].weight;
            }
        }
    } else { // tp == MIN or tp == MAX
        if (ar.type==DEFN) {
            if (ar.expr->c==p) {
                // NB: we're not using the stack now; assert that each of the used literals is on it, before p.
                if (tp==MIN) {
                    for (int i=0; i<ar.set->min && ar.set->set[i].weight<ar.expr->min; ++i)
                        lits.push(ar.set->set[i].lit);
                    assert(ar.set->max<ar.set->set.size() && ar.set->set[ar.set->max].weight >= ar.expr->min && ar.set->set[ar.set->max].weight <= ar.expr->max);
                    lits.push(~ar.set->set[ar.set->max].lit);
                } else { // tp==MAX
                    for (int i=ar.set->set.size()-1; i>ar.set->max && ar.set->set[i].weight>ar.expr->max; --i)
                        lits.push(ar.set->set[i].lit);
                    assert(ar.set->min>=0 && ar.set->set[ar.set->min].weight >= ar.expr->min && ar.set->set[ar.set->min].weight <= ar.expr->max);
                    lits.push(~ar.set->set[ar.set->min].lit);
                }
            } else {assert(ar.expr->c==~p);
                // either the real MIN/MAX is too small, or too big.
                if (tp==MIN) {
                    if (ar.set->max < ar.set->set.size() && ar.set->set[ar.set->max].weight<ar.expr->min) {
                        reportf("First option; ar.set->max=%d; its weight=%d; ar.expr->min=%d.\n",ar.set->max,ar.set->set[ar.set->max].weight,ar.expr->min);
                        lits.push(~ar.set->stack[ar.set->max].lit);
                    } else {
                        assert(ar.set->max == ar.set->set.size() || ar.set->set[ar.set->min].weight>ar.expr->max); // NOTE: this does not assert that all these literals are on stack before p.
                        reportf("Second option; ar.expr->max=%d.\n",ar.expr->max);
                        for (int i=0; i<ar.set->set.size() && ar.set->set[i].weight<=ar.expr->max; ++i)
                            lits.push(ar.set->set[i].lit);
                    }
                } else { // tp==MAX
                    if (ar.set->min >= 0 && ar.set->set[ar.set->min].weight>ar.expr->max)
                        lits.push(~ar.set->stack[ar.set->min].lit);
                    else {
                        assert(ar.set->min < 0 || ar.set->set[ar.set->max].weight<ar.expr->min); // NOTE: this does not assert that all these literals are on stack before p.
                        for (int i=ar.set->set.size()-1; i>=0 && ar.set->set[i].weight>=ar.expr->min; ++i)
                            lits.push(ar.set->set[i].lit);
                    }
                }
            }
        } else if (ar.type==POS) { assert(false); // This type of propagation should not occur as long as the (@&) TODO's haven't been implemented.
/*            if (value(ar.expr->c)==l_True) {
                lits.push(~ar.expr->c);
            } else { assert(value(ar.expr->c)==l_False);
                lits.push(ar.expr->c);
            }
*/
        } else { assert(ar.type==NEG);
            if (tp==MIN) {
                if (value(ar.expr->c)==l_True) // assert that p's weight is < ar.expr->min
                    lits.push(~ar.expr->c);
                else { assert(value(ar.expr->c)==l_False);
                    lits.push(ar.expr->c);
                    for (int i=0; i<ar.set->set.size() && ar.set->set[i].weight < ar.expr->min; ++i)
                        lits.push(ar.set->set[i].lit); // assert that these literals are on the stack, before p.
                }
            } else { // tp==MAX
                if (value(ar.expr->c)==l_True) // assert that p's weight is > ar.expr->max
                    lits.push(~ar.expr->c);
                else { assert(value(ar.expr->c)==l_False);
                    lits.push(ar.expr->c);
                    for (int i=ar.set->set.size()-1; i>=0 && ar.set->set[i].weight > ar.expr->max; ++i)
                        lits.push(ar.set->set[i].lit); // assert that these literals are on the stack, before p.
                }
            }
        }
    }

    Clause* c = Clause_new(lits, true);
    if (verbosity>=2) {reportf("Implicit reason clause for "); printLit(p); reportf(" : "); printClause(*c); reportf("\n");}

    return c;
}

/*_________________________________________________________________________________________________
  |
  |  reduceDB : ()  ->  [void]
  |  
  |  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity()); } };
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt());
    for (i = j = 0; i < learnts.size() / 2; i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]))
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() < extra_lim)
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
}


void Solver::removeSatisfied(vec<Clause*>& cs)
{
    int i,j;
    for (i = j = 0; i < cs.size(); i++){
        if (satisfied(*cs[i]))
            removeClause(*cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    // Note that ecnf_mode.init is still true, if this is the first time running simplify!
    ecnf_mode.init=false;
    bool old_ecnf_def = ecnf_mode.def; ecnf_mode.def=false;
    if (!ok || propagate() != NULL)
        return ok = false;
    ecnf_mode.def=old_ecnf_def;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    // Initialization procedure to ensure correctness of subsequent indirectPropagate() calls.
    // This has to be done before the first choice.
    if (ecnf_mode.def && conflicts==0) {
        // NOTE: we're doing a stable model initialization here. No need for a loop.
        cf_justification_disj.clear(); cf_justification_disj.growTo(nVars());
        sp_justification_disj.clear(); sp_justification_disj.growTo(nVars());
        cf_justification_aggr.clear(); cf_justification_aggr.growTo(2*nVars());
        sp_justification_aggr.clear(); sp_justification_aggr.growTo(2*nVars());

        vec<int> nb_body_lits_to_justify;           // Note: use as boolean for DISJ and AGGR, as int for CONJ.
        nb_body_lits_to_justify.growTo(nVars(), 0); // Unless there are big conjunctions, we could use 'seen' instead of 'nb_body_lits_to_justify'.
        
        // *** First : initialize nb_body_lits_to_justify, and the propagation queue propq.
        for (int i=0; i<defdVars.size(); i++) {
            Var v = defdVars[i];
            if (value(v)==l_False) continue;
            switch (defType[v]) {
                case DISJ: nb_body_lits_to_justify[v]=1;
                           break;
                case CONJ: nb_body_lits_to_justify[v]=definition[v]->size()-1;
                           break;
                case AGGR: nb_body_lits_to_justify[v]=1;
                           break;
                default:   break;
            }
        }

        // *** Next: initialize a queue of literals that are safe with regard to cycle-freeness. (i.e.: either are not in justification, or are justified in a cycle-free way.)
        Queue<Lit> propq;
        for (int i=0; i<nVars(); ++i) if (value(i)!=l_True) propq.insert(Lit(i,true)); // First all non-false negative literals.
        for (int i=0; i<nVars(); ++i)
            if (defType[i]==NONDEF && value(i)!=l_False)
                propq.insert(Lit(i,false));                      // Then all non-false non-defined positive literals.

        // *** Next: propagate safeness to defined literals until fixpoint.
        // While we do this, we build the initial justification.
        while (propq.size() > 0) {
            Lit l=propq.peek(); propq.pop();

            for (int i=0; i<disj_occurs[toInt(l)].size(); ++i) { // Find disjunctions that may be made cycle-safe through l.
                Var v=(disj_occurs[toInt(l)])[i];
                if (defType[v]==NONDEF || value(v)==l_False) continue;
                assert(defType[v]==DISJ);
                if (nb_body_lits_to_justify[v]>0) {
                    nb_body_lits_to_justify[v]=0;
                    propq.insert(Lit(v,false));
                    cf_justification_disj[v]=l;
                    sp_justification_disj[v]=l;
                }
            }
            for (int i=0; i<conj_occurs[toInt(l)].size(); ++i) { // Find conjunctions that may be made cycle-safe through l.
                Var v=(conj_occurs[toInt(l)])[i];
                if (defType[v]==NONDEF || value(v)==l_False) continue;
                assert(defType[v]==CONJ);
                --nb_body_lits_to_justify[v];
                if (nb_body_lits_to_justify[v]==0)
                    propq.insert(Lit(v,false));
            }
            if (ecnf_mode.aggr) { // TODO
                for (int i=0; i<Aggr_watches[var(l)].size(); ++i) {         // Find aggregate expressions that may be made cycle-safe through l.
                    AggrWatch& aw=(Aggr_watches[var(l)])[i];
                    if (aw.type==DEFN) continue;
                    vec<AggrExpr*>& exprs = aw.set->exprs;
                    for (int j=0; j<exprs.size(); ++j) {
                        Var v=var(exprs[j]->c);
                        if (defType[v]==NONDEF || value(v)==l_False) continue;
                        assert(defType[v]==AGGR);
                        if (nb_body_lits_to_justify[v]>0) {
                            vec<Lit> jstf; // Only add it if complete (!nb_body_lits_to_justify[v]).
                            vec<AggrSet::WLit>& lits = aw.set->set;
                            switch (aw.set->type) {
                                case SUM:{
                                             int min=0; int max=aw.set->cmax;
                                             bool complete=false;
                                             for (int k=0; !complete && k<lits.size(); ++k) {
                                                 Lit ll=lits[k].lit;
                                                 if (value(ll)!=l_False) {
                                                     if (sign(ll) || nb_body_lits_to_justify[var(ll)]==0) {
                                                         jstf.push(ll);
                                                         min+=lits[k].weight;
                                                         if (min>=exprs[j]->min && max<=exprs[j]->max) complete=true;
                                                     }
                                                 }
                                                 if (value(ll)!=l_True) {
                                                     if (!sign(ll) || nb_body_lits_to_justify[var(ll)]==0) {
                                                         jstf.push(~ll);
                                                         max-=lits[k].weight;
                                                         if (min>=exprs[j]->min && max<=exprs[j]->max) complete=true;
                                                     }
                                                 }
                                             }
                                             if (complete) 
                                                 nb_body_lits_to_justify[v]=0;
                                             break;}
                                case PROD:{
                                              int min=1; int max=aw.set->cmax;
                                              bool complete=false;
                                              for (int k=0; !complete && k<lits.size(); ++k) {
                                                  Lit ll=lits[k].lit;
                                                  if (value(ll)!=l_False) {
                                                      if (sign(ll) || nb_body_lits_to_justify[var(ll)]==0) {
                                                          jstf.push(ll);
                                                          min*=lits[k].weight;
                                                          if (min>=exprs[j]->min && max<=exprs[j]->max) complete=true;
                                                      }
                                                  }
                                                  if (value(ll)!=l_True) {
                                                      if (!sign(ll) || nb_body_lits_to_justify[var(ll)]==0) {
                                                          jstf.push(~ll);
                                                          max=max/lits[k].weight;
                                                          if (min>=exprs[j]->min && max<=exprs[j]->max) complete=true;
                                                      }
                                                  }
                                              }
                                              if (complete) 
                                                  nb_body_lits_to_justify[v]=0;
                                              break;}
                                case MIN:{
                                             bool aux=true;
                                             int k=0; for (; aux && lits[k].weight<exprs[j]->min; ++k) {
                                                 Lit ll = lits[k].lit;
                                                 if (!sign(ll) || nb_body_lits_to_justify[var(ll)]==0)
                                                     jstf.push(~ll);
                                                 else
                                                     aux=false;
                                             }// NB: 'aux' switches meaning inbetween here...
                                             for (; aux && lits[k].weight<=exprs[j]->max; ++k) {
                                                 Lit ll = lits[k].lit;
                                                 if (value(ll)!=l_False && (sign(ll) || nb_body_lits_to_justify[var(ll)]==0)) {
                                                     jstf.push(ll);
                                                     aux=false;
                                                 }
                                             }
                                             if (!aux)
                                                 nb_body_lits_to_justify[v]=0;
                                             break;}
                                case MAX:{
                                             bool aux=true;
                                             int k=lits.size()-1; for (; aux && lits[k].weight>exprs[j]->max; --k) {
                                                 Lit ll = lits[k].lit;
                                                 if (!sign(ll) || nb_body_lits_to_justify[var(ll)]==0)
                                                     jstf.push(~ll);
                                                 else
                                                     aux=false;
                                             }// NB: 'aux' switches meaning inbetween here...
                                             for (; aux && lits[k].weight>=exprs[j]->min; --k) {
                                                 Lit ll = lits[k].lit;
                                                 if (value(ll)!=l_False && (!sign(ll) || !nb_body_lits_to_justify[var(ll)])) {
                                                     jstf.push(ll);
                                                     aux=false;
                                                 }
                                             }
                                             if (!aux)
                                                 nb_body_lits_to_justify[v]=0;
                                             break;}
                            }
                            if (nb_body_lits_to_justify[v]==0) {
                                propq.insert(Lit(v,false));
                                assert(sp_justification_aggr[v].size()==0);
                                assert(cf_justification_aggr[v].size()==0);
                                for (int j=0; j<jstf.size(); ++j) {
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
        int trs = trail.size();
        if (verbosity>=2) reportf("Initialization of justification makes these atoms false: [");
        vec<Lit> empty;
        for (int i=0; i<defdVars.size(); i++) {
            Var v = defdVars[i];
            if (nb_body_lits_to_justify[v]>0) {
                if (verbosity>=2) reportf(" %d",v+1);
                if (!enqueue(Lit(v,true)))
                    return ok = false;
                defType[v]=NONDEF;
                --atoms_in_pos_loops;
            }
        }
        if (verbosity>=2) reportf(" ]\n");

        if (trail.size()>trs) { // There is stuff to propagate now.
            if (atoms_in_pos_loops==0)
                ecnf_mode.def = false;
            ecnf_mode.init=false;
            if (propagate() != NULL) // NOTE: this includes the first round of indirectPropagate()!! Make sure first time ALL cycle sources are searched.
                return ok = false;
        }

        if (atoms_in_pos_loops==0 && verbosity>=1)
            reportf("| All recursive atoms falsified in initializations.                           |\n");
        //if (ecnf_mode.def && verbosity>=2) assert(isCycleFree()); // Only for debugging!!
    }

    if (verbosity>=2 && (ecnf_mode.amo || ecnf_mode.def || ecnf_mode.aggr))
        reportf("ECNF data structures initialized and theory simplified.\n");

    ecnf_mode.init=false;
    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts, int nof_learnts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

    bool first = true;

    for (;;){
        if (maxruntime>0.0 && cpuTime()>maxruntime) {
            reportf("| Exceeded maximum search time; now terminating search.                       |\n");
            reportf("===============================================================================\n");
            ok = false;
            return l_False;
        }
        if (verbosity>=2) reportf("Starting decision level %d.\n",trail_lim.size());
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
                if (verbosity>=2) {reportf("Adding learnt clause: [ "); printLit(learnt_clause[0]); reportf(" ], backtracking until level %d.\n",backtrack_level);}
            }else{
                Clause* c = Clause_new(learnt_clause, true);
                learnts.push(c);
                attachClause(*c);
                claBumpActivity(*c);
                uncheckedEnqueue(learnt_clause[0], c);
                if (verbosity>=2) {reportf("Adding learnt clause: [ "); printClause(*c); reportf("], backtracking until level %d.\n",backtrack_level);}
            }

            varDecayActivity();
            claDecayActivity();

        }else{
            // NO CONFLICT

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    if (verbosity>=2) {reportf("Add assumption literal "); printLit(p); reportf(" to the trail.\n");}
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
                if (verbosity>=2) {reportf("Choice literal: "); printLit(next); reportf(".\n");}
            }

            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

void Solver::invalidateModel(const vec<Lit>& lits, int& init_qhead) {
    cancelUntil(0);
    if (init_qhead<qhead)
        cancelFurther(init_qhead);

    if (lits.size() == 1){
        uncheckedEnqueue(lits[0]);
        ++init_qhead;
    }else{
        Clause* c = Clause_new(lits, false);
        clauses.push(c);
        if (verbosity>=2) {reportf("Adding model-invalidating clause: [ "); printClause(*c); reportf("]\n");}
        attachClause(*c);
    }

    varDecayActivity();
    claDecayActivity();
}

bool Solver::solve()
{
    if (!ok) return false;
    bool solved=true;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    if (ecnf_mode.mnmz && to_minimize.size()==0)
        ecnf_mode.mnmz = false;
    if (ecnf_mode.mnmz)
        remove_satisfied = false;

    int init_qhead = qhead;
    for (int n = nb_models; nb_models==0 || n>0; n--) {

        bool rslt=false;
        vec<Lit> assmpt;
        vec<Lit> learnt;
        if (!ecnf_mode.mnmz)
            rslt = solve(assmpt);  // The standard: solve with empty assumptions.
        else {
            assumptions.clear();

            vec<lbool> cp_model;
            while (solve(assmpt)) {
                if (verbosity>=2) {
                    reportf("Found a (perhaps non-minimal) model: [");
                    for (int i=0;i<model.size();i++)
                        if (model[i]!=l_Undef)
                            reportf(" %s%d",(model[i]==l_True ? "":"-"), i+1);
                    reportf(" ]\n");
                    reportf("To minimize: [");
                    for (int i=0;i<to_minimize.size();i++) {
                        reportf(" ");printLit(to_minimize[i]);
                    }
                    reportf(" ]\n");
                }

                // save the model that was just found
                cp_model.clear();
                for (int i=0;i<model.size();i++)
                    cp_model.push(model[i]);
                // create a new set of assumptions, and add a new learned clause, based on this model and on the mnmz set
                assmpt.clear();
                learnt.clear();
                for (int i=0;i<to_minimize.size();i++) {
                    Lit li=~to_minimize[i];
                    if (sign(li) == (cp_model[var(li)]==l_True))
                        learnt.push(li);
                    else
                        assmpt.push(li);
                }

                if (learnt.size()>0)
                    invalidateModel(learnt,init_qhead);
                else
                    break; // The found model is certainly already minimal.  TODO make sure no more attempts at finding new model are tried?
            }
            if (cp_model.size()>0) {
                model.clear();
                for (int i=0;i<cp_model.size();i++)
                    model.push(cp_model[i]);
                cp_model.clear();
                rslt=true;
            }
        }

        if (rslt) {
            if (nb_models==1) {
                printf("SATISFIABLE\n");
            } else if (verbosity >= 1)
                printf("%d model%s found.\n",nb_models-n+1,nb_models==n?"":"s");
            if (res != NULL) {
                if (n==nb_models)
                    fprintf(res, "SAT\n");
                for (int i = 0; i < nVars(); i++)
                    if (model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            }
            if (n>1 || nb_models==0) {
                if (trail_lim.size()+assmpt.size()==0) {
                    if (nb_models!=1 && verbosity >= 1)
                        printf("There are no more models.\n");
                    break;
                } else {
                    learnt.clear();
                    // Add negation of model as learnt clause for next iteration.
                    for (int i=0; i<trail_lim.size(); i++)
                        learnt.push(~trail[trail_lim[i]]);
                    for (int i=0; i<assmpt.size(); i++)
                        learnt.push(~assmpt[i]);
                    // Remove doubles.
                    sort(learnt);
                    Lit p; int i, j;
                    for (i = j = 0, p = lit_Undef; i < learnt.size(); i++)
                        if (learnt[i] != p)
                            learnt[j++] = p = learnt[i];
                    learnt.shrink(i - j);
                    invalidateModel(learnt,init_qhead);
                }
            }
        } else {
            if (nb_models==1 || n==nb_models) {
                printf("UNSATISFIABLE\n");
                if (res != NULL)
                    fprintf(res, "UNSAT\n");
                solved=false;
            }
            break;
        }
    }
    cancelUntil(0);

    if (res != NULL)
        fclose(res);

    if (verbosity >= 1)
        reportf("===============================================================================\n");

    return solved;
}

bool Solver::solve(const vec<Lit>& assumps)
{
    model.clear();
    conflict.clear();

    if (!ok) return false;

    assumps.copyTo(assumptions);

    double  nof_conflicts = restart_first;
    double  nof_learnts   = nClauses() * learntsize_factor;
    lbool   status = l_Undef;

    // Search:
    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= restart_inc;
        nof_learnts   *= learntsize_inc;
        // TODO: if ecnf_mode.def, then do final check for well-foundedness, using "defdVars", for situations like P <- ~Q, Q <- ~P.
    }
    learntsize_inc = (9+learntsize_inc)/10; // For multiple models, make sure the allowed number of learnt clauses doesn't increase too rapidly.

    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
#ifndef NDEBUG
        verifyModel();
#endif
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }

    return status == l_True;
}

//=================================================================================================
// Debug methods:


void Solver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++){
        assert(clauses[i]->mark() == 0);
        Clause& c = *clauses[i];
        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        reportf("unsatisfied clause: ");
        printClause(*clauses[i]);
        reportf("\n");
        failed = true;
    next:;
    }

    assert(!failed);

    if (verbosity>=2)
        reportf("Verified %d original clauses.\n", clauses.size());
}


void Solver::checkLiteralCount()
{
    // Check that sizes are calculated correctly:
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0)
            cnt += clauses[i]->size();

    if ((int)clauses_literals != cnt){
        fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
        assert((int)clauses_literals == cnt);
    }
}

/*
void Solver::fwIndirectPropagate() { // TODO doesn't work yet with recursive aggregates. probably the building of the loop formula is only remaining thing.
    for (int i=0; i<defdVars.size(); i++) {
        Var v = defdVars[i];
        if (defType[v]==DISJ && value(v)!=l_False) {
            // Find out whether it has unknown disjuncts. (Non-false, but if they are already true, there is nothing to propagate.)
            Clause &rl = *definition[v];
            for (int j=0; j<rl.size(); j++) {
                if (rl[j]!=Lit(v,true) && value(rl[j])==l_Undef) {
                    // Make it false, and if necessary, change v's supporting justification.
                    assigns[var(rl[j])] = toInt(l_False);
                    bool chj=false;
                    if ((sp_justification_fw[v])[0]==rl[j]) {
                        chj=true;
                        int k=0;
                        for (; k<rl.size(); k++)
                            if (k!=j && rl[k]!=Lit(v,true) && value(rl[k])!=l_False) break;
                        if (k==rl.size()) { // No alternative literal has been found, i.e., all body literals are now false. Then there is certainly no cycle through v without rl[j].
                            assigns[var(rl[j])] = toInt(l_Undef);
                            break;
                        } else
                            change_jstfc(v,rl[k]);
                    }

                    // See if the disjunctively defined atom is in a cycle like this.
                    css.clear();
                    css.add(v);
                    std::set<Var> ufs;
                    bool ufs_found = unfounded(v, ufs);
                    fw_propagation_attempts++;

                    // Set back the disjunct's truth value, and the supporting justification if it was changed.
                    assigns[var(rl[j])] = toInt(l_Undef);
                    if (chj) change_jstfc(v,rl[j]);

                    // We have found a cycle, and therefore a forward propagation, iff ufs contains a true atom.
                    if (ufs_found) {
                        std::set<Var>::iterator tch = ufs.begin();
                        for (; tch != ufs.end(); tch++)
                            if (value(*tch)==l_True) break;
                        if (tch!=ufs.end()) {
                            // Add the loop formula and make the propagation.
                            vec<Lit> loopf;
                            loopf.push(rl[j]);
                            loopf.push(Lit(*tch, true));
                            for (std::set<Var>::iterator uit = ufs.begin(); uit != ufs.end(); uit++) {
                                if (verbosity>=2) {printClause(*definition[*uit]); reportf("\n");}
                                if (defType[*uit]==DISJ) {
                                    Clause& cl = *definition[*uit];
                                    for (int l=0; l<cl.size(); l++) {
                                        Lit bdl = cl[l];
                                        if (bdl != Lit(*uit,true) && bdl!=rl[j] && seen[var(bdl)]!=(sign(bdl)?1:2) && ufs.find(var(bdl)) == ufs.end()) {
                                            loopf.push(bdl);
                                            seen[var(bdl)]=(sign(bdl)?1:2); // Just in case P and ~P both appear; otherwise we might get something between well-founded and ultimate semantics...
                                        }
                                    }
                                }
                            }
                            // clear "seen" again.
                            for (int l=0; l<loopf.size(); l++) seen[var(loopf[l])]=0;
                            // Do the propagation, using the loop formula as reason clause.
                            Clause* c = Clause_new(loopf, true);
                            if (verbosity>=2) {reportf("Forward propagation: "); printClause(*c); reportf("\n");}
                            learnts.push(c); attachClause(*c); claBumpActivity(*c);
                            uncheckedEnqueue(loopf[0], c);
                            fw_propagations++;
                            return;
                        }
                    }

                }
            }
        }
    }
}
*/


bool Solver::isCycleFree() { // currently only when no recursice aggregates!! TODO
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
