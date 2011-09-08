/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

MiniSat 09z -- Copyright (c) 2009, Markus Iser, Carsten Sinz


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

#include "Solver.hpp"
#include "mtl/Sort.h"
#include <cmath>

/*AB*/
#include <vector>
#include <iostream>
#include <cstdarg>

using namespace std;
using namespace Minisat;
using namespace MinisatID;
/*AE*/

//=================================================================================================
// Constructor/Destructor:

void Minisat::reportf(const char* format, ...){
	fflush(stdout);
    va_list args;
    va_start(args, format);
	fprintf(stderr, format, args);
	fflush(stderr);
}

Solver::Solver(PCSolver& s/*A*/) :
	solver(s), /*A*/
	choicestaken(0), /*A*/
	useheur(true), /*A*/
    // Parameters: (formerly in 'SearchParams')
    var_decay(1 / 0.95), clause_decay(1 / 0.999), random_var_freq(0.02), learntsize_inc(1.1)

    // More parameters:
    //
  , expensive_ccmin  (true)
  , polarity_mode    (polarity_stored)
  , verbosity        (0)
  , random_seed      (91648253)

    // Statistics: (formerly in 'SolverStats')
    //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok               (true)
  , cla_inc          (1)
  , var_inc          (1)
  , qhead            (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , progress_estimate(0)
  , remove_satisfied (true/*A*/)
  /*AB*/, backtrackLevels(NULL)/*AE*/
{}


Solver::~Solver()
{
    for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) free(clauses[i]);

    /*AB*/
    if(backtrackLevels!=NULL){
    	delete[] backtrackLevels;
    }
    /*AE*/
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

	polarity.push(false);
    decision_var.push((char)dvar);

    insertVarOrder(v);
    return v;
}

/*AB*/

/**
 * This is (currently) necessary, because the intialization schema is the following:
 *
 * add elements: /
 * add unit clause: PROPAGATION
 * add aggregate: /
 *
 * finishDatastructures:
 * 		initialize all aggregates and propagate the already derived atoms in them
 *
 */
//void Solver::finishParsing(){
//	qhead = 0;
//}

std::vector<Lit> Solver::getDecisions()const {
	std::vector<Lit> v;
	for(int i=0; i<trail_lim.size(); i++){
		v.push_back(trail[trail_lim[i]]);
	}
	return v;
}

void Solver::addLearnedClause(Clause* c){
	if(c->size()>1){
		learnts.push(c);
		attachClause(*c);
		if(/*AB*/useheur/*AE*/){
			claBumpActivity(*c);
		}
		if(verbosity>=3){
			reportf("Learned clause added: ");
			printClause(*c);
			reportf("\n");
		}
	}else{
		assert(c->size()==1);
		cancelUntil(0);
		vec<Lit> ps;
		ps.push(c->operator [](0));
		addClause(ps);
	}
}

bool Solver::totalModelFound(){
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

/*std::vector<Clause*> Solver::getClausesWhichOnlyContain(const std::vector<Var>& vars){
	std::vector<Clause*> matches;
	for(int i=0; i<clauses.size(); i++){
		bool allmatch = true;
		for(int j=0; allmatch && j<clauses[i]->size(); j++){
			bool found = false;
			for(int k=0; !found && k<vars.size(); k++){
				if(var(clauses[i]->operator[] (j))==vars[k]){
					found = true;
				}
			}
			if(!found){
				allmatch = false;
			}
		}
		if(allmatch){
			matches.push_back(clauses[i]);
		}
	}
	return matches;
}*/

void Solver::removeAllLearnedClauses(){
	for (int i = 0; i < learnts.size(); i++){
		removeClause(*learnts[i]);
	}
	learnts.clear();
}

bool Solver::addClause(vec<Lit>& ps, Clause*& newclause){
	assert(decisionLevel() == 0);

	if (!ok){
		return false;
	}
	sort(ps);
	assert(ps.size()>1);

	Clause* c = Clause_new(ps, false);
	clauses.push(c);
	attachClause(*c);
	newclause = c;

	return true;
}

/*AE*/


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

/*AB*/
//@pre: cs and clauses are both ordered according to time added
void Solver::removeClauses(const std::vector<Clause*>& cs) {
	int i, j, k = 0;
	for (i = j = 0; i < clauses.size(); i++){
	    if(k<cs.size() && cs[k]==clauses[i]){
	    	removeClause(*cs[k++]);
	    }else{
	    	clauses[j++] = clauses[i];
	    }
	}
	assert(cs.size()==k);
	clauses.shrink(i - j);
}
/*AE*/

void Solver::removeClause(Clause& c) {
    detachClause(c);
    free(&c); }


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
    	/*AB*/Lit decision = trail[trail_lim[level]];
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var     x  = var(trail[c]);
            assigns[x] = toInt(l_Undef);
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        /*AB*/
        int levels = trail_lim.size() - level;
        trail_lim.shrink(levels);
        solver.backtrackDecisionLevel(levels, level, decision);
        /*AE*/
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;

    /*AB*/
    //Forced decision if available:
    while(choicestaken<forcedchoices.size() && value(forcedchoices[choicestaken])!=l_Undef){
		reportf("Forced choice already propagated\n");
		choicestaken++;
	}
	if(choicestaken<forcedchoices.size()){
		return forcedchoices[choicestaken++];
	}
    /*AE*/

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

    /*AB*/
    if(next==var_Undef){
    	return lit_Undef;
    }
    /*AE*/

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_stored:  sign = polarity[next]; break; /* MODIFIED 2009 */
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    default: assert(false); }

    /*AB*/ //omdat anders polarity[next] als eens durft crashen
    return Lit(next, sign);
    /*AE*/
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
bool Solver::isAlreadyUsedInAnalyze(const Lit& lit) const{
	return seen[var(lit)]==1;
}
bool Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    /*AB VERY IMPORTANT*/
	int lvl = 0;
	for (int i = 0; i < confl->size(); i++){
		int litlevel = level[var(confl->operator [](i))];
		if (litlevel > lvl){
			lvl = litlevel;
		}
	}
	cancelUntil(lvl);
	assert(lvl==decisionLevel());
	assert(confl!=NULL);

	std::vector<Lit> explain;
	if(verbosity>4){
		reportf("Choices: ");
		for(int i=0; i<trail_lim.size(); i++){
			clog <<trail[trail_lim[i]] <<" ";
		}
		reportf("\n");
		reportf("Trail: \n");
		for(int i=0; i<trail_lim.size()-1; i++){
			clog <<"Level: ";
			for(int j=trail_lim[i]; j<trail_lim[i+1]; j++){
				clog <<trail[j] <<" ";
			}
			clog <<"\n";
		}
		clog <<"Level: ";
		for(int j=trail_lim[trail_lim.size()-1]; j<trail.size(); j++){
			clog <<trail[j] <<" ";
		}
		clog <<"\n";
	}
	/*AE*/

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    bool deleteImplicitClause = false;
    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

        /*AB*/
        if(verbosity>4){
        	reportf("    ------------------------------------- \n");
			reportf("        Current conflict clause: ");
			printClause(c);
			reportf("\n");
			reportf("        Current learned clause: ");
			for (int i = 1; i < out_learnt.size(); i++) {
				printLit(out_learnt[i]);
				reportf(" ");
			}
			reportf("\n");

		}
    	/*AE*/

        if (c.learnt() /*AB*/&& useheur /*AE*/)
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level[var(q)] > 0){
            	if(/*AB*/ useheur /*AE*/){
            		varBumpActivity(var(q));
            	}
                seen[var(q)] = 1;
                if (level[var(q)] >= decisionLevel()){
                	/*AB*/
                	if(verbosity>4){
                    	explain.push_back(q);
            		}
                	/*AE*/
                    pathC++;
                }else{
                	/*AB INCORRECT IDEA*/
                	//might it help here to filter out literals that were not decision literals?
                	//Important: take care that q is added if its decision variable is not in the clause!
                	/*AE*/

					out_learnt.push(q);
					if (level[var(q)] > out_btlevel)
						out_btlevel = level[var(q)];

                }
            }
        }

        /*AB*/
        if(verbosity>4){
        	clog <<"        Still to explain: ";
        	for(std::vector<Lit>::const_iterator i=explain.begin(); i<explain.end(); i++){
        		clog <<*i <<" ";
        	}
        	clog <<"\n";
		}

        if(deleteImplicitClause){
        	delete confl;
        	deleteImplicitClause = false;
        }
        /*AE*/

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason[var(p)];

		/*AB*/
        if(solver.symmetryPropagationOnAnalyze(p)){
        	return true;
        }

        if(verbosity>4){
			reportf("    Now getting explanation for ");
			for(std::vector<Lit>::iterator i=explain.begin(); i<explain.end(); i++){
				if(var(*i)==var(p)){
					explain.erase(i);
					break;
				}
			}
			printLit(p);
			reportf(" => ");
		}

        if(confl==NULL && pathC>1){
			confl = solver.getExplanation(p);
			deleteImplicitClause = true;
        }
        if(verbosity>4 && confl!=NULL) {
        	printClause(*confl); reportf("\n");
        }
        /*AE*/

        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    if(verbosity>=3){
    	clog <<"FINAL learned clause";
    	for(int i=0; i<out_learnt.size(); i++){
    		clog <<out_learnt[i] <<" ";
    	}
    	clog <<"\n";
	}

    if(verbosity>4){
    	clog <<"End clause learning: explanation found\n";
    }

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

    /*AB*/
	return false;
	/*AE*/
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


void Solver::uncheckedEnqueue(Lit p, Clause* from)
{
    assert(value(p) == l_Undef);
    assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
    level   [var(p)] = decisionLevel();
    reason  [var(p)] = from;
    polarity[var(p)] = sign(p); /* Modified 2009 */
    trail.push(p);
    /*AB*/
    if(verbosity>=5){
    	solver.printEnqueued(p);
    }
    /*AE*/
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
                    confl = &c;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }else
                    uncheckedEnqueue(first, &c);
            }
        FoundWatch:;
        }
        ws.shrink(i - j);
        /*AB*/
        //Important: standard propagate returns a conflict clause that ALREADY exists in the clause store
        //so these functions should return POINTERS OWNED BY SOMEONE ELSE
		if(confl==NULL){
			confl = solver.propagate(p);
		}
		if(qhead==trail.size() && confl==NULL){
        	confl = solver.propagateAtEndOfQueue();
		}
		if(confl!=NULL){
			qhead = trail.size();
		}
        /*AE*/
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
    nof_learnts   *= learntsize_inc; /* Modified 2009 */
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

    if (!ok || propagate() != NULL)
    	return ok = false;

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

    return true;
}


/*_________________________________________________________________________________________________
|
|  search ->  [lbool]
|
|  Description:
|    Search for a model
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on restart-strategy.
|________________________________________________________________________________________________@*/
lbool Solver::search(/*AB*/bool nosearch/*AE*/)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

    bool first = true;

    for (;;){
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0)
            	return l_False;

            first = false;

            learnt_clause.clear();

            bool symmetrybacktrack = analyze(confl, learnt_clause, backtrack_level);

            if(symmetrybacktrack){
				cancelUntil(decisionLevel()-1);
				continue;
            }

            cancelUntil(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

			backtrackLevels[conflicts % restartMore]= backtrack_level;

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                Clause* c = Clause_new(learnt_clause, true);
                learnts.push(c);
                attachClause(*c);
                if(/*AB*/useheur/*AE*/){
                	claBumpActivity(*c);
                }
                uncheckedEnqueue(learnt_clause[0], c);
            }

            varDecayActivity();
            claDecayActivity();

        }else{
            // NO CONFLICT
            if (conflictC >= restartMore) {  /* Modified 2009 */
            	// search and count local minimum
				int LM= backtrackLevels[0];
				int nofLM= 1;

				for(int i=1; i< restartMore; i++) {
					if(backtrackLevels[i]< LM) {
						LM= backtrackLevels[i];
						nofLM= 1;
					} else if(backtrackLevels[i]== LM) {
						nofLM++;
					}
				}

				if(LM > restartTolerance && nofLM>= restartLess) { /* Modified 2009 */
					// AVOIDANCE OF PLATEAUX
	                progress_estimate= progressEstimate();
    	            cancelUntil(0);
        	        return l_Undef;
				}
			}

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && /*AB*/ !solver.simplify() /*AE*/)
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
                    break;
                }
            }

            if (next == lit_Undef){
            	/*AB*/
            	if(nosearch){
            		return true;
            	}
            	/*AE*/

                // New variable decision:
                decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef){
                    // Model found:
                    return l_True;
				}

                /*AB*/
				if (verbosity >= 1) {
					solver.printChoiceMade(decisionLevel(), next);
				}
				/*AE*/
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


bool Solver::solve(const vec<Lit>& assumps /*AB*/, bool nosearch /*AE*/)
{
    model.clear();
    conflict.clear();

    if (!ok) return false;

    assumps.copyTo(assumptions);

	/* Modified 2009 */
	double cvr= (double)nClauses() / (double)nVars();
    nof_learnts= 300000 / cvr;
	restartLess= 5;
	restartMore= 42;
	restartTolerance= nVars() / 10000 +10;
	/*AB*/
	if(backtrackLevels != NULL){
		delete[] backtrackLevels;
	}
	/*AE*/
	backtrackLevels= new int[restartMore];

    lbool   status        = l_Undef;

    // Search:
    while (status == l_Undef){
    	status = search(/*AB*/nosearch/*AE*/);
    	/*AB*/
    	if(nosearch){
    		return status==l_True;
    	}
    	status = solver.checkStatus(status);
    	/*AE*/
    }

    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
/*AB*/
#ifndef NDEBUG
        verifyModel();
#endif
/*AE*/
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }

    /*A*///cancelUntil(0);
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

    if(verbosity>3){
    	reportf("Verified %d original clauses.\n", clauses.size());
    }
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

/*AB*/
void Solver::printStatistics() const{
	std::clog << "> restarts              : " <<starts <<"\n";
	std::clog << "> conflicts             : " <<decisions <<"  (" <<(float)rnd_decisions*100 / (float)decisions <<" % random)\n";
	std::clog << "> decisions             : " <<starts <<"\n";
	std::clog << "> propagations          : " <<propagations <<"\n";
	std::clog << "> conflict literals     : " <<tot_literals <<"  (" <<((max_literals-tot_literals)*100/(double)max_literals) <<" % deleted)\n";
}
/*AE*/