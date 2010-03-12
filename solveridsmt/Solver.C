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

#include <limits.h>

//=================================================================================================
// Constructor/Destructor:

Solver::Solver() :
	optim(NONE), head(0),

	// Parameters: (formerly in 'SearchParams')
	res(NULL), nb_models(1),modelsfound(0),
	var_decay(1 / 0.95),
	clause_decay(1 / 0.999),
	random_var_freq(0.02),
	restart_first(100),
	restart_inc(1.5),
	learntsize_factor((double) 1 / (double) 3),
	learntsize_inc(1.1)

	// More parameters:
	,
	expensive_ccmin(true),
	polarity_mode(polarity_false),
	random_seed(91648253),
	maxruntime(0.0)

	// Statistics: (formerly in 'SolverStats')
	,
	starts(0),
	decisions(0),
	rnd_decisions(0),
	propagations(0),
	conflicts(0),
	clauses_literals(0),
	learnts_literals(0),
	max_literals(0),
	tot_literals(0),

	qhead(0),

	ok(true),
	remove_satisfied(false),
	/*
	 * FIXME: Als removesatisfied aanstaat, blijkt hij door een bug (die ik niet helemaal begrijp),
	 * ook backtrackt over het stuk trail dat de propagaties bevat VOORDAT er gezocht wordt. Maar als
	 * hun clauses verwijderd zijn (want er wordt normaal bijgehouden dat die literals altijd waar zijn),
	 * dan zijn er dus inconsistenties. Zie bij invalidatemodel met cancelfurther
	 * het idee is dat propagaties voor de search (of voordat naar een volgend
	 * model wordt gezocht) gemaakt worden en dat over die propagaties niet gebacktrackt wordt.
	 */

	cla_inc(1), var_inc(1), simpDB_assigns(-1),
	simpDB_props(0),
	progress_estimate(0), order_heap(VarOrderLt(activity)){
}

Solver::~Solver() {
	for (int i = 0; i < learnts.size(); i++)
		free(learnts[i]);
	for (int i = 0; i < clauses.size(); i++)
		free(clauses[i]);
}

//=================================================================================================
// Minor methods:

// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar) {
	int v = nVars();
	watches .push(); // (list for positive literal)
	watches .push(); // (list for negative literal)
	reason .push(NULL);
	assigns .push(toInt(l_Undef));
	level .push(-1);
	activity .push(0);
	seen .push(0);

	polarity .push((char) sign);
	decision_var.push((char) dvar);

	//////////////START TSOLVER
	if(tsolver!=NULL){
		tsolver->notifyVarAdded();
	}
	if(aggsolver!=NULL){
		aggsolver->notifyVarAdded();
	}
	//////////////END TSOLVER

	insertVarOrder(v);
	return v;
}

//////////////START TSOLVER
/**
 * Used to notify the sat solver that all tsolver datastructures have been initialized.
 * The sat solver will then reset the q-pointer to the start, so all literals already on the queue are repropagated in due course.
 */
void Solver::finishParsing(){
	qhead = 0;
}

bool Solver::existsUnknownVar(){
	Var v = var_Undef;
	while (v == var_Undef || toLbool(assigns[v]) != l_Undef || !decision_var[v]) {
		if (v != var_Undef)
			order_heap.removeMin();
		if (order_heap.empty()) {
			v = var_Undef;
			break;
		} else
			v = order_heap[0];
	}
	return v==var_Undef;
}
//////////////END TSOLVER

bool Solver::addClause(vec<Lit>& ps) {
	assert(decisionLevel() == 0);

	if (!ok){
		return false;
	}

	// Check if clause is satisfied and remove false/duplicate literals:
	sort(ps);
	Lit p;
	int i, j;
	for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
		if (value(ps[i]) == l_True || ps[i] == ~p)
			return true;
		else if (value(ps[i]) != l_False && ps[i] != p)
			ps[j++] = p = ps[i];
	ps.shrink(i - j);

	if (ps.size() == 0)
		return ok = false;
	else if (ps.size() == 1) {
		assert(value(ps[0]) == l_Undef);
		setTrue(ps[0]);
		if(verbosity>=2){
    		reportf("Clause added: ");
			printLit(ps[0]);
			reportf("\n");
		}
		return ok = (propagate() == NULL);
	} else {
		Clause* c = Clause_new(ps, false);
		clauses.push(c);
		attachClause(*c);
		if(verbosity>=3){
			reportf("Clause added: ");
			printClause(*c);
		}
	}

	return true;
}

/////////START TSOLVER
void Solver::addLearnedClause(Clause* c){
	learnts.push(c);
	attachClause(*c);
	claBumpActivity(*c);
	if(verbosity>=3){
		reportf("Learned clause added: ");
		printClause(*c);
	}
}
/////////END TSOLVER

void Solver::attachClause(Clause& c) {
	assert(c.size() > 1);
	watches[toInt(~c[0])].push(&c);
	watches[toInt(~c[1])].push(&c);
	if (c.learnt())
		learnts_literals += c.size();
	else
		clauses_literals += c.size();
}

void Solver::detachClause(Clause& c) {
	assert(c.size() > 1);
	assert(find(watches[toInt(~c[0])], &c));
	assert(find(watches[toInt(~c[1])], &c));
	remove(watches[toInt(~c[0])], &c);
	remove(watches[toInt(~c[1])], &c);
	if (c.learnt())
		learnts_literals -= c.size();
	else
		clauses_literals -= c.size();
}

void Solver::removeClause(Clause& c) {
	detachClause(c);
	free(&c);
}

bool Solver::satisfied(const Clause& c) const {
	for (int i = 0; i < c.size(); i++)
		if (value(c[i]) == l_True)
			return true;
	return false;
}

///////////////START CHANGES
// Can be used to go beyond level 0!
void Solver::cancelFurther(int init_qhead) {
	for (int c = trail.size() - 1; c >= init_qhead; c--) {
		Var x = var(trail[c]);
		assigns[x] = toInt(l_Undef);
		insertVarOrder(x);
		//////////////START TSOLVER
		if(tsolver!=NULL){
			tsolver->backtrack(trail[c]);
		}
		if(aggsolver!=NULL){
			aggsolver->backtrack(trail[c]);
		}
		//////////////END TSOLVER
	}

	qhead = init_qhead;
	trail.shrink(trail.size() - qhead);
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::backtrackTo(int level) {
	if (decisionLevel() > level) {
		cancelFurther(trail_lim[level]);
		trail_lim.shrink(trail_lim.size() - level);
	}
}
///////////////END CHANGES


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(int polarity_mode, double random_var_freq) {
	Var next = var_Undef;

	// Random decision:
	if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
		next = order_heap[irand(random_seed, order_heap.size())];
		if (toLbool(assigns[next]) == l_Undef && decision_var[next])
			rnd_decisions++;
	}

	// Activity based decision:
	while (next == var_Undef || toLbool(assigns[next]) != l_Undef
			|| !decision_var[next])
		if (order_heap.empty()) {
			next = var_Undef;
			break;
		} else
			next = order_heap.removeMin();

	bool sign = false;
	switch (polarity_mode) {
	case polarity_true:
		sign = false;
		break;
	case polarity_false:
		sign = true;
		break;
	case polarity_user:
		sign = polarity[next];
		break;
	case polarity_rnd:
		sign = irand(random_seed, 2);
		break;
	default:
		assert(false);
	}

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
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel) {
	int pathC = 0;
	Lit p = lit_Undef;

	// Generate conflict clause:
	//
	out_learnt.push(); // (leave room for the asserting literal)
	int index = trail.size() - 1;
	out_btlevel = 0;

	//////////////START TSOLVER
	bool deleteImplicitClause = false;
	//////////////END TSOLVER
	do {
		assert(confl != NULL); // (otherwise should be UIP)
		Clause& c = *confl;

		if(verbosity>2){
			reportf("Current conflict clause: ");
			printClause(c);
			reportf("Current learned clause: ");
			for(int i=0; i<out_learnt.size();i++){
				printLit(out_learnt[i]); reportf(" ");
			}
			reportf("\n");
		}

		if (c.learnt())
			claBumpActivity(c);

		for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
			Lit q = c[j];

			if (!seen[var(q)] && level[var(q)] > 0) {
				varBumpActivity(var(q));
				seen[var(q)] = 1;
				if (level[var(q)] >= decisionLevel())
					pathC++;
				else {
					out_learnt.push(q);
					if (level[var(q)] > out_btlevel)
						out_btlevel = level[var(q)];
				}
			}
		}

		//////////////START TSOLVER
		if (deleteImplicitClause) {
			delete confl;
			deleteImplicitClause = false;
		}
		//////////////END TSOLVER

		// Select next clause to look at:
		while (!seen[var(trail[index--])])
			;
		p = trail[index + 1];

		if(verbosity>2){
			reportf("Getting explanation for ");
			printLit(p);reportf("\n");
		}

		confl = reason[var(p)];

		//////////////START TSOLVER
		if (aggsolver!=NULL && confl == NULL && pathC > 1) {
			confl = aggsolver->getExplanation(p);
			deleteImplicitClause = true;
		}
		//////////////END TSOLVER
		seen[var(p)] = 0;
		pathC--;

	} while (pathC > 0);
	out_learnt[0] = ~p;

	// Simplify conflict clause:
	//
	int i, j;
	if (expensive_ccmin) {
		uint32_t abstract_level = 0;
		for (i = 1; i < out_learnt.size(); i++)
			abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

		out_learnt.copyTo(analyze_toclear);
		for (i = j = 1; i < out_learnt.size(); i++)
			if (reason[var(out_learnt[i])] == NULL || !litRedundant(
					out_learnt[i], abstract_level))
				out_learnt[j++] = out_learnt[i];
	} else {
		out_learnt.copyTo(analyze_toclear);
		for (i = j = 1; i < out_learnt.size(); i++) {
			Clause& c = *reason[var(out_learnt[i])];
			for (int k = 1; k < c.size(); k++)
				if (!seen[var(c[k])] && level[var(c[k])] > 0) {
					out_learnt[j++] = out_learnt[i];
					break;
				}
		}
	}
	max_literals += out_learnt.size();
	out_learnt.shrink(i - j);
	tot_literals += out_learnt.size();

	// Find correct backtrack level:
	//
	if (out_learnt.size() == 1)
		out_btlevel = 0;
	else {
		int max_i = 1;
		for (int i = 2; i < out_learnt.size(); i++)
			if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
				max_i = i;
		Lit p = out_learnt[max_i];
		out_learnt[max_i] = out_learnt[1];
		out_learnt[1] = p;
		out_btlevel = level[var(p)];
	}

	for (int j = 0; j < analyze_toclear.size(); j++)
		seen[var(analyze_toclear[j])] = 0; // ('seen[]' is now cleared)
}

// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels) {
	analyze_stack.clear();
	analyze_stack.push(p);
	int top = analyze_toclear.size();
	while (analyze_stack.size() > 0) {
		assert(reason[var(analyze_stack.last())] != NULL);
		Clause& c = *reason[var(analyze_stack.last())];
		analyze_stack.pop();

		for (int i = 1; i < c.size(); i++) {
			Lit p = c[i];
			if (!seen[var(p)] && level[var(p)] > 0) {
				if (reason[var(p)] != NULL && (abstractLevel(var(p))
						& abstract_levels) != 0) {
					seen[var(p)] = 1;
					analyze_stack.push(p);
					analyze_toclear.push(p);
				} else {
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
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict) {
	out_conflict.clear();
	out_conflict.push(p);

	if (decisionLevel() == 0)
		return;

	seen[var(p)] = 1;

	for (int i = trail.size() - 1; i >= trail_lim[0]; i--) {
		Var x = var(trail[i]);
		if (seen[x]) {
			if (reason[x] == NULL) {
				assert(level[x] > 0);
				out_conflict.push(~trail[i]);
			} else {
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

void Solver::setTrue(Lit p, Clause* from) {
	assert(value(p) == l_Undef);
	assigns[var(p)] = toInt(lbool(!sign(p))); // <<== abstract but not uttermost effecient
	level[var(p)] = decisionLevel();
	reason[var(p)] = from;
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
Clause* Solver::propagate() {
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
                for (int k = 2; k < c.size(); k++){
                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[toInt(~c[1])].push(&c);
                        goto FoundWatch;
                    }
                }

				// Did not find watch -- clause is unit under assignment:
				*j++ = &c;
				if (value(first) == l_False){
					if (verbosity>=2) reportf(" Conflict");
					confl = &c;
					qhead = trail.size();
					// Copy the remaining watches:
					while (i < end){
						*j++ = *i++;
					}
				}else {
					setTrue(first, &c);
					if (verbosity>=2) {reportf(" "); printLit(first);}
				}
            }
FoundWatch:;
        }
        ws.shrink(i - j);
        if (verbosity>=2) reportf(" ).\n");

		//////////////START TSOLVER
        if(aggsolver!=NULL && confl == NULL){
        	confl = aggsolver->propagate(p);
        }
        if(tsolver!=NULL && confl == NULL){
			confl = tsolver->propagate(p);
		}
		if(qhead==trail.size() && confl==NULL && tsolver!=NULL){
			confl = tsolver->propagateDefinitions();
		}
		if(confl!=NULL){
			qhead = trail.size();
		}
		//////////////END TSOLVER
	}

	propagations += num_props;
	simpDB_props -= num_props;
	return confl;
}

/*_________________________________________________________________________________________________
 |
 |  reduceDB : ()  ->  [void]
 |
 |  Description:
 |    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
 |    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
 |________________________________________________________________________________________________@*/
struct reduceDB_lt {
	bool operator ()(Clause* x, Clause* y) {
		return x->size() > 2 && (y->size() == 2 || x->activity()
				< y->activity());
	}
};
void Solver::reduceDB() {
	int i, j;
	double extra_lim = cla_inc / learnts.size(); // Remove any clause below this activity

	sort(learnts, reduceDB_lt());
	for (i = j = 0; i < learnts.size() / 2; i++) {
		if (learnts[i]->size() > 2 && !locked(*learnts[i]))
			removeClause(*learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	for (; i < learnts.size(); i++) {
		if (learnts[i]->size() > 2 && !locked(*learnts[i])
				&& learnts[i]->activity() < extra_lim)
			removeClause(*learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	learnts.shrink(i - j);
}

void Solver::removeSatisfied(vec<Clause*>& cs) {
	int i, j;
	for (i = j = 0; i < cs.size(); i++) {
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
bool Solver::simplify() {
	assert(decisionLevel() == 0);

	if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
		return true;

	// Remove satisfied clauses:
	removeSatisfied(learnts);
	if (remove_satisfied) // Can be turned off.
		removeSatisfied(clauses);

	// Remove fixed variables from the variable heap:
	order_heap.filter(VarFilter(*this));

	simpDB_assigns = nAssigns();
	simpDB_props = clauses_literals + learnts_literals; // (shouldn't depend on stats really, but it will do for now)

    //////////////START TSOLVER
	if(conflicts==0 && (tsolver!=NULL && !tsolver->simplify())){
		ok = false;
		return false;
	}

	// There might be stuff to propagate now.
	if (propagate()!=NULL) { // NOTE: this includes the first round of indirectPropagate()!! Make sure first time ALL cycle sources are searched.
		ok = false;
		return false;
	}

	// Important: DO NOT PROPAGATE BEFORE SIMPLIFY!!! (TODO CHANGE CODE TO ALLOW THIS!)
	//////////////END TSOLVER

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
lbool Solver::search(int nof_conflicts, int nof_learnts) {
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

        if (verbosity>=4 && trail_lim.size()==0){
        	reportf("CLAUSES\n");
        	for(int i=0; i<clauses.size(); i++){
        		printClause(*clauses[i]);
        	}
        	reportf("LEARNTS\n");
        	for(int i=0; i<learnts.size(); i++){
				printClause(*learnts[i]);
			}
        	reportf("END\n");
        }

        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            backtrackTo(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
            	//FIXME: dit wordt bij backtracken dus meteen vergeten?
            	setTrue(learnt_clause[0]);
                if (verbosity>=2) {reportf("Adding learnt clause: [ "); printLit(learnt_clause[0]); reportf(" ], backtracking until level %d.\n",backtrack_level);}
            }else{
                Clause* c = Clause_new(learnt_clause, true);
                addLearnedClause(c);
                setTrue(learnt_clause[0], c);
                if (verbosity>=2) {reportf("Adding learnt clause: [ "); printClause(*c); reportf("], backtracking until level %d.\n",backtrack_level);}
            }

            varDecayActivity();
            claDecayActivity();

        }else{
            // NO CONFLICT

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                backtrackTo(0);
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
            setTrue(next);
        }
    }
}

double Solver::progressEstimate() const {
	double progress = 0;
	double F = 1.0 / nVars();

	for (int i = 0; i <= decisionLevel(); i++) {
		int beg = i == 0 ? 0 : trail_lim[i - 1];
		int end = i == decisionLevel() ? trail.size() : trail_lim[i];
		progress += pow(F, i) * (end - beg);
	}

	return progress / nVars();
}

////////////START TSOLVER
void Solver::invalidateModel(vec<Lit>& learnt) {
	//FIXME: do not backtrack to 0, but do analyzefinal on learnt to check to which level to backtrack.
	//for subsetminimize this is not so clear, because assumptions have to be added too, so maybe there backtrack to 0 is necessary (for unit propagation before search)
	backtrackTo(0);

	//FIXME: hier werd soms verder gebacktrackt dan het laagste decision level (in de unit propagaties dus)
	//maar geen idee waarom dit nodig was. Mss toch eens nakijken?

	if (verbosity>=3) {	reportf("Adding model-invalidating clause: [ "); }
	addClause(learnt);
	if (verbosity>=3) {	reportf("]\n"); }

	varDecayActivity();
	claDecayActivity();
}

/////////////////////// START OF EXTENSIONS
//TODO in andere solver?
void Solver::addMinimize(const vec<Lit>& lits, bool subset) {
	/*TODO if (!ecnf_mode.mnmz)
		reportf("ERROR! Attempt at adding a subset minimize statement, though ECNF specifiers did not contain \"mnmz\".\n"), exit(3);*/
	if (lits.size() == 0) {
		reportf("Error: The set of literals to be minimized is empty,\n");
		exit(3);
	}
	if (optim!=NONE) {
		reportf("At most one set of literals to be minimized can be given.\n");
		exit(3);
	}

	if(subset){
		optim = SUBSETMNMZ;
	}else{
		optim = MNMZ;
	}

	for (int i = 0; i < lits.size(); i++){
		to_minimize.push(lits[i]);
	}
}

void Solver::addSumMinimize(const Var head, const int setid){
	/*TODO if (!ecnf_mode.mnmz)
		reportf("ERROR! Attempt at adding a subset minimize statement, though ECNF specifiers did not contain \"mnmz\".\n"), exit(3);*/
	if (optim!=NONE) {
		reportf("Only one optimization statement is possible.\n");
		exit(3);
	}

	optim = SUMMNMZ;
	this->head = head;
	vec<Lit> cl;
	cl.push(Lit(head, false));
	addClause(cl);
	getAggSolver()->addMnmzSum(head, setid, false);
}

/**
 * Checks satisfiability of the theory.
 * If no model is found or no more models exist, false is returned. True otherwise
 * If a model is found, it is printed and returned in <m>, the theory is extended to prevent
 * 		the same model from being found again and
 * 		the datastructures are reset to prepare to find the next model
 */
/**
 * Important: assmpt are the first DECISIONS that are made. So they are not automatic unit propagations
 * and can be backtracked!
 * FIXME: een mooier design maken zodat het duidelijk is naarwaar gebacktrackt moet worden (tot voor of tot
 * na de assumptions, afhankelijk van of ze voor alle modellen moeten gelden of alleen voor het huidige).
 */
bool Solver::findNext(const vec<Lit>& assmpt, vec<Lit>& m){
	bool rslt = solve(assmpt);

	if(rslt){
		modelsfound++;

		printModel();

		for (int i = 0; i < nVars(); i++){
			if (model[i] != l_Undef){
				m.push(model[i]==l_True?Lit(i, false):Lit(i, true));
			}
		}

		//check if more models can exist
		if (trail_lim.size() /*FIXME + assmpts.size() */!= 0) { //choices were made, so other models possible
			vec<Lit> invalidation;
			invalidate(invalidation);
			invalidateModel(invalidation);
		}else{
			rslt = false; //no more models possible
		}
	}

	return rslt;
}

void Solver::printModel(){
	if (modelsfound==1) {
		fprintf(res==NULL?stdout:res, "SAT\n");
		if(verbosity>=1){
			printf("SATISFIABLE\n");
		}
	}

	if(nb_models!=1){
		printf("%d model%s found.\n", modelsfound, modelsfound>1 ? "s" : "");
	}

	for (int i = 0; i < nVars(); i++){
		if (model[i] != l_Undef){
			fprintf(res==NULL?stdout:res, "%s%s%d", (i == 0) ? "" : " ", (model[i]== l_True) ? "" : "-", i + 1);
		}
	}
	fprintf(res==NULL?stdout:res, " 0\n");
}

bool Solver::solve(){
	bool solved = false;

	//TODO check that it is only called once
	if (!ok){
		fprintf(res==NULL?stdout:res, "UNSAT\n");
		return false;
	}

	if (verbosity >= 1) {
		reportf("============================[ Search Statistics ]==============================\n");
		reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
		reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
		reportf("===============================================================================\n");
	}

try{
	modelsfound = 0;
	bool moremodels = true;

	if(optim!=NONE){
		vec<Lit> assmpt;
		vec<Lit> model;
		findOptimal(assmpt, model);
	}else{
		while(moremodels && (nb_models==0 || modelsfound<nb_models)){
			vec<Lit> assmpt;
			vec<Lit> model;
			moremodels = findNext(assmpt, model);
		}
	}

	if(modelsfound==0){
		printf("UNSATISFIABLE\n");
		fprintf(res==NULL?stdout:res, "UNSAT\n");
	}else if(!moremodels && nb_models!=1){
		printf("There are no more models.\n");
	}

	if(nb_models==0 || nb_models==modelsfound){
		solved = true;
	}else{
		solved = false;
	}

	if (res != NULL){
		fclose(res);
	}

	if (verbosity >= 1){
		reportf("===============================================================================\n");
	}

	}catch(UNSAT x){
		//FIXME:
		reportf("Dit staat nog op de verkeerde plaats");
		assert(false);
		solved = false;
	}
	return solved;
}

void Solver::invalidate(vec<Lit>& invalidation){
	// Add negation of model as clause for next iteration.
	//add all choice literals
	for (int i = 0; i < trail_lim.size(); i++){
		invalidation.push(~trail[trail_lim[i]]);
	}
	//add all assumptions
	/*for (int i = 0; i < assmpt.size(); i++){
		learnt.push(~assmpt[i]);
	}*/
	// Remove doubles.
	sort(invalidation);
	Lit p = lit_Undef;
	int i=0, j=0;
	for (; i < invalidation.size(); i++){
		if (invalidation[i] != p){
			invalidation[j++] = (p = invalidation[i]);
		}
	}
	invalidation.shrink(i - j);
}

bool Solver::invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt){
	int subsetsize = 0;

	for(int i=0; i<to_minimize.size(); i++){
		if(model[i]==l_True){
			invalidation.push(~to_minimize[i]);
			subsetsize++;
		}else{
			assmpt.push(~to_minimize[i]);
		}
	}

	if(subsetsize==0){
		return true; //optimum has already been found!!!
	}else{
		return false;
	}
}

bool Solver::invalidateValue(vec<Lit>& invalidation){
	bool currentoptimumfound = false;

	for(int i=0; !currentoptimumfound && i<to_minimize.size(); i++){
		if(!currentoptimumfound && model[i]==l_True){
			currentoptimumfound = true;
		}
		if(!currentoptimumfound){
			invalidation.push(to_minimize[i]);
		}
	}

	if(invalidation.size()==0){
		return true; //optimum has already been found!!!
	}else{
		return false;
	}
}

/*
 * If the optimum possible value is reached, the model is not invalidated. Otherwise, unsat has to be found first, so it is invalidated.
 * FIXME: add code that allows to reset the solver when the optimal value has been found, to search for more models with the same optimal value.
 *
 * Returns true if an optimal model was found
 */
bool Solver::findOptimal(vec<Lit>& assmpt, vec<Lit>& m){
	bool rslt = true, hasmodels = false, optimumreached = false;
	while(!optimumreached && rslt){
		if(optim==SUMMNMZ){
			//Noodzakelijk om de aanpassingen aan de bound door te propageren.
			aggsolver->propagateMnmz(head);
		}
		rslt = solve(assmpt);

		if(rslt && !optimumreached){
			if(!hasmodels){
				hasmodels = true;
			}

			m.clear();
			for (int i = 0; i < nVars(); i++){
				if (model[i] != l_Undef){
					m.push(model[i]==l_True?Lit(i, false):Lit(i, true));
				}
			}

			vec<Lit> invalidation;
			switch(optim){
			case MNMZ:
				optimumreached = invalidateValue(invalidation);
				break;
			case SUBSETMNMZ:
				assmpt.clear();
				optimumreached = invalidateSubset(invalidation, assmpt);
				break;
			case SUMMNMZ:
				//FIXME the invalidation turns out to be empty
				optimumreached = getAggSolver()->invalidateSum(invalidation, head);
				break;
			case NONE:
				assert(false);
				break;
			}

			if(!optimumreached){
				if (trail_lim.size() /*FIXME + assmpts.size() */!= 0) { //choices were made, so other models possible
					invalidateModel(invalidation);
				}else{
					optimumreached = true;
				}
			}

			if(verbosity>2){
				printf("Temporary model: \n");
				for (int i = 0; i < nVars(); i++){
					printf("%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "" : "-", i + 1);
				}
				printf(" 0\n");
			}

		}else if(!rslt){
			optimumreached = true;
		}
	}

	if(!hasmodels){
		assert(!optimumreached);
		fprintf(res==NULL?stdout:res, " UNSAT\n");
		printf("UNSATISFIABLE\n");
	}else{
		assert(optimumreached);
		fprintf(res==NULL?stdout:res, " SAT\n");
		printf("SATISFIABLE\n");
		for (int i = 0; i < nVars(); i++){
			fprintf(res==NULL?stdout:res, "%s%s%d", (i == 0) ? "" : " ", !sign(m[i]) ? "" : "-", i + 1);
		}
		fprintf(res==NULL?stdout:res, " 0\n");

		modelsfound++;
	}

	return optimumreached;
}

bool Solver::solve(const vec<Lit>& assumps) {
	model.clear();
	conflict.clear();

	if (!ok)
		return false;

	assumps.copyTo(assumptions);

	double nof_conflicts = restart_first;
	double nof_learnts = nClauses() * learntsize_factor;
	lbool status = l_Undef;

	// Search:
	while (status == l_Undef) {
		if (verbosity >= 1)
			reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
		status = search((int) nof_conflicts, (int) nof_learnts);
		nof_conflicts *= restart_inc;
		nof_learnts *= learntsize_inc;
		if(status==l_True && tsolver!=NULL){
			bool wellfounded = tsolver->isWellFoundedModel();
			if(verbosity>=1){
				reportf("The model is %s.\n", wellfounded?"well-founded":"stable but not well-founded");
			}
			if(!wellfounded){
				status=l_False;
			}
		}
	}
	learntsize_inc = (9 + learntsize_inc) / 10; // For multiple models, make sure the allowed number of learnt clauses doesn't increase too rapidly.

	if (status == l_True) {
		// Extend & copy model:
		model.growTo(nVars());
		for (int i = 0; i < nVars(); i++)
			model[i] = value(i);
#ifndef NDEBUG
		verifyModel();
#endif
	} else {
		assert(status == l_False);
		if (conflict.size() == 0)
			ok = false;
	}

	return status == l_True;
}

//=================================================================================================
// Debug methods:


void Solver::verifyModel() {
	bool failed = false;
	for (int i = 0; i < clauses.size(); i++) {
		assert(clauses[i]->mark() == 0);
		Clause& c = *clauses[i];
		for (int j = 0; j < c.size(); j++)
			if (modelValue(c[j]) == l_True)
				goto next;

		reportf("unsatisfied clause: ");
		printClause(*clauses[i]);
		reportf("\n");
		failed = true;
		next: ;
	}

	assert(!failed);

	if (verbosity >= 2)
		reportf("Verified %d original clauses.\n", clauses.size());
}

void Solver::checkLiteralCount() {
	// Check that sizes are calculated correctly:
	int cnt = 0;
	for (int i = 0; i < clauses.size(); i++)
		if (clauses[i]->mark() == 0)
			cnt += clauses[i]->size();

	if ((int) clauses_literals != cnt) {
		fprintf(stderr, "literal count: %d, real value = %d\n",
				(int) clauses_literals, cnt);
		assert((int)clauses_literals == cnt);
	}
}

//============================================================================================================

/*
 void Solver::fwIndirectPropagate() { // doesn't work yet with recursive aggregates. probably the building of the loop formula is only remaining thing.
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
