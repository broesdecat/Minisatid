/***************************************************************************************[Solver.cc]
 Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 Copyright (c) 2007-2010, Niklas Sorensson

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

#include <cmath>
#include <cstdio>

#include "mtl/Sort.h"
#include "mtl/Alg.h"

#include <sstream>
#include <cstdarg>
#include <algorithm>

#include "utils/Utils.hpp"
#include "utils/Print.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "constraintvisitors/ConstraintVisitor.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

//=================================================================================================
// Options:

static const char* _cat = "CORE";

static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false));
static DoubleOption opt_random_var_freq(_cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable", 0,
		DoubleRange(0, true, 1, true));
static DoubleOption opt_random_seed(_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption opt_phase_saving(_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption opt_rnd_init_act(_cat, "rnd-init", "Randomize the initial activity", false);
static BoolOption opt_luby_restart(_cat, "luby", "Use the Luby restart sequence", true);
static IntOption opt_restart_first(_cat, "rfirst", "The base restart interval", 100, IntRange(1, INT32_MAX));
static IntOption opt_maxlearned(_cat, "maxlearned", "The maximum number of learned clauses", INT32_MAX, IntRange(1, INT32_MAX));
static DoubleOption opt_restart_inc(_cat, "rinc", "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption opt_garbage_frac(_cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20,
		DoubleRange(0, false, HUGE_VAL, false));

//=================================================================================================
// Constructor/Destructor:

Solver::Solver(PCSolver* s, bool oneshot) :
		Propagator(s, "satsolver"), random_var_freq(opt_random_var_freq), random_seed(opt_random_seed), verbosity(getPCSolver().verbosity()), var_decay(
				opt_var_decay), rnd_pol(false), max_learned_clauses(opt_maxlearned), oneshot(oneshot), assumpset(false), needsimplify(true), backtracked(
				true),

		clause_decay(opt_clause_decay), luby_restart(opt_luby_restart), ccmin_mode(opt_ccmin_mode), phase_saving(opt_phase_saving), rnd_init_act(
				opt_rnd_init_act), garbage_frac(opt_garbage_frac), restart_first(opt_restart_first), restart_inc(opt_restart_inc)

		// Parameters (the rest):
				, learntsize_factor((double) 1 / (double) 3), learntsize_inc(1.1)

		// Parameters (experimental):
				, learntsize_adjust_start_confl(100), learntsize_adjust_inc(1.5)

		// Statistics: (formerly in 'SolverStats')
				, starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(
				0), tot_literals(0), ok(true), cla_inc(1), var_inc(1), watches(WatcherDeleted(ca)), qhead(0), simpDB_assigns(-1), simpDB_props(0), order_heap(
				VarOrderLt(activity)), remove_satisfied(true) {
	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_PROPAGATE);
}

Solver::~Solver() {
}

// VARIABLE CREATION

void Solver::setDecidable(Var v, bool decide) { // NOTE: no-op if already a decision var!
	bool newdecidable = decide && not decision[v];
	if (newdecidable) {
		dec_vars++;
	} else if (not decide && decision[v]){
		dec_vars--;
	}else{
		return;
	}

	if (verbosity > 10) {
		if (decide) {
			clog << ">>> Making " << toString(v) << " decidable.\n";
		} else if (not decide && decision[v]) {
			clog << ">>> Making decidable " << toString(v) << " undecidable.\n";
		}
	}

	decision[v] = decide;
	insertVarOrder(v);

	if (newdecidable) {
		getPCSolver().notifyBecameDecidable(v);
	}
}

// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
Var Solver::newVar(lbool upol, bool dvar) {
	int v = nVars();
	watches.init(mkLit(v, false));
	watches.init(mkLit(v, true));
	assigns.push(l_Undef);
	vardata.push(mkVarData(CRef_Undef, 0));
	//activity .push(0);
	activity.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
	seen.push(0);

	//if(getPCSolver().modes().lazy){
	//	polarity.push(((float)rand()/ RAND_MAX)>0.5);
	//}else{
	polarity.push(true);
	//}

	user_pol.push(upol);
	decision.push();
	trail.capacity(v + 1);
	setDecidable(v, dvar);
	return v;
}

inline void Solver::createNewDecisionLevel() {
	trail_lim.push(trail.size());
	getPCSolver().newDecisionLevel();
}

std::vector<Lit> Solver::getDecisions() const {
	std::vector<Lit> v;
	auto prev = -1;
	for (int i = 0; i < trail_lim.size(); i++) {
		if(trail_lim[i]==prev){ // Prev was a dummy decision level
			continue;
		}
		prev = trail_lim[i];
		v.push_back(trail[trail_lim[i]]);
	}
	return v;
}

// CLAUSE MANAGEMENT

struct permute {
	int newposition;
	Lit value;
	permute(int newpos, Lit value) :
			newposition(newpos), value(value) {
	}
};

struct lessthan_permute {
	bool operator()(const permute& lhs, const permute& rhs) {
		return lhs.newposition < rhs.newposition;
	}
};

// NOTE: do not reimplement as sort with a random comparison operator, comparison should be CONSISTENT on consecutive calls!
void permuteRandomly(vec<Lit>& lits) {
	vector<permute> newpositions;
	for (int i = 0; i < lits.size(); ++i) {
		newpositions.push_back(permute(rand(), lits[i]));
	}
	std::sort(newpositions.begin(), newpositions.end(), lessthan_permute());
	for (int i = 0; i < lits.size(); ++i) {
		lits[i] = newpositions[i].value;
	}
}

// NOTE: only used for generating explanations
CRef Solver::makeClause(const std::vector<Lit>& lits, bool learnt) {
	vec<Lit> ps;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ps.push(*i);
	}
	return ca.alloc(ps, learnt);
}

/*
 * reverse trail:
 * 	list of pairs <Lit, level>
 * 		until backtrack lower than level, after each backtrack immediately propagate Lit in notifyPropagate
 */

/*
 * Delete all literals true at the root
 * If all false, backtrack to level of latest literal
 * If size == 0
 * 		ok = false
 * If size == 1
 * 		settrue literal
 * 		add to reverse trail <literal, 0>
 * If size larger
 * 		add to watch structure
 */
bool Solver::addClause(const std::vector<Lit>& lits) {
	if (!ok) {
		return false;
	}

	vec<Lit> ps;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		ps.push(*i);
	}

	sort(ps); // NOTE: remove duplicates

	// Check satisfaction and remove literals false at root
	Lit p;
	int i, j;
	for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
		if (rootValue(ps[i]) == l_True || ps[i] == ~p) {
			return true;
		} else if (rootValue(ps[i]) != l_False && ps[i] != p) {
			ps[j++] = p = ps[i];
		}
	}
	ps.shrinkByNb(i - j);

	// NOTE: sort randomly to reduce dependency on grounding and literal introduction mechanics (certainly for lazy grounding)
	permuteRandomly(ps);

	if (ps.size() == 0) {
		return ok = false;
	} else if (ps.size() == 1) {
		if (decisionLevel() > 0) {
			if(value(ps[0]) == l_False) {
				getPCSolver().backtrackTo(getLevel(var(ps[0])) - 1); // NOTE: Certainly not root level, would have found out otherwise
			}
			MAssert(value(ps[0])!=l_False);
			auto clause = getPCSolver().createClause(Disjunction( { ps[0] }), false);
			addRootUnitLit(ReverseTrailElem(ps[0], 0, clause));
			checkedEnqueue(ps[0], clause);
		} else {
			uncheckedEnqueue(ps[0]);
		}
		return ok = (propagate() == CRef_Undef); // FIXME add methods should return the conflict clause if applicable
	} else {
		CRef cr = ca.alloc(ps, false);
		addToClauses(cr, false);
		attachClause(cr);
	}

	return true;
}

// NOTE: linked to createClause and the dummy variables
void Solver::addLearnedClause(CRef rc) {
	auto& c = ca[rc];
	MAssert(c.size() > 1);
	addToClauses(rc, true);
	attachClause(rc);
	claBumpActivity(c);
	if (verbosity >= 3) {
		clog << "Learned clause added: ";
		printClause(rc);
		clog << "\n";
	}
}

void swap(Clause& c, int from, int to) {
	MAssert(c.size()>from && c.size()>to);
	auto temp = c[from];
	c[from] = c[to];
	c[to] = temp;
}

void Solver::addRootUnitLit(const ReverseTrailElem& elem){
	rootunitlits.push_back(elem);
	savedrootlits.insert(rootunitlits.back());
}

/*
 * if both false
 * 		backtrack to latest level
 * if can propagate lit
 * 		propagate lit
 * 		add to reverse trail <lit, level of second latest literal>
 * add to watches, lit and second latest literal as watch
 */
void Solver::attachClause(CRef cr) {
	auto& c = ca[cr];
	MAssert(c.size() > 1);

	// If level>0, the clause can contain true and false literals
	// If not a learned clause, the order of literals is not required to guarantee correctness
	// So need code to restructure the clause for correct watch addition and handle the case where all literals are false or unit propagation possible
	if (decisionLevel() > 0 && not c.learnt()) {
		int nonfalse1 = -1, nonfalse2 = -1, recentfalse1 = -1, recentfalse2 = -1; // literal indices: 1 is "1st", 2 is "2nd"
		for (int i = 0; i < c.size(); ++i) {
			if (isFalse(c[i])) {
				auto currentlevel = getLevel(var(c[i]));
				auto mostrecentfalse = recentfalse1 == -1 ? -1 : getLevel(var(c[recentfalse1]));
				auto most2ndrecentfalse = recentfalse2 == -1 ? -1 : getLevel(var(c[recentfalse2]));
				if (currentlevel >= mostrecentfalse) {
					recentfalse2 = recentfalse1;
					recentfalse1 = i;
				} else if (currentlevel > most2ndrecentfalse) {
					recentfalse2 = i;
				}
			} else {
				if (nonfalse1 == -1) {
					nonfalse1 = i;
				} else if (nonfalse2 == -1) {
					nonfalse2 = i;
				}
			}
		}

		MAssert(nonfalse1==-1 || not isFalse(c[nonfalse1]));
		MAssert(nonfalse2==-1 || not isFalse(c[nonfalse2]));

		if (nonfalse1 == -1) { // Conflict
			getPCSolver().backtrackTo(getLevel(var(c[recentfalse1])) - 1);
			nonfalse1 = recentfalse1;
			MAssert(nonfalse2==-1 || not isFalse(c[nonfalse2]));
			if (not isFalse(c[recentfalse2])) {
				nonfalse2 = recentfalse2;
			} else {
				recentfalse1 = recentfalse2;
			}
		}

		// At least one literal unknown
		MAssert(nonfalse1!=-1 && not isFalse(c[nonfalse1]));
		MAssert(nonfalse2==-1 || not isFalse(c[nonfalse2]));
		swap(c, nonfalse1, 0);
		if (recentfalse1 == 0) {
			recentfalse1 = nonfalse1;
		}
		if (nonfalse2 == 0) {
			nonfalse2 = nonfalse1;
		}
		MAssert(not isFalse(c[0]));
		MAssert(nonfalse2==-1 || not isFalse(c[nonfalse2]));

		if (nonfalse2 != -1) { // Two literals non-false: normal case
			MAssert(not isFalse(c[nonfalse2]));
			swap(c, nonfalse2, 1);
			MAssert(not isFalse(c[1]));
		} else { // Clause is unit
			MAssert(recentfalse1!=-1 && isFalse(c[recentfalse1]));
			swap(c, recentfalse1, 1);
			MAssert(isFalse(c[1]));
			MAssert(value(c[0])==l_Undef);
			checkedEnqueue(c[0], cr);
			addRootUnitLit(ReverseTrailElem(c[0], getLevel(var(c[1])), cr));
		}
	}

	if (not c.learnt()) {
		MAssert(not isFalse(c[1]) || not isFalse(c[0]));
	}
	watches[~c[0]].push(Watcher(cr, c[1]));
	watches[~c[1]].push(Watcher(cr, c[0]));

	if (not c.learnt() || not isFalse(c[0]) || not isFalse(c[1])) {
		checkDecisionVars(c);
	}

	if (c.learnt()) {
		learnts_literals += c.size();
	} else {
		clauses_literals += c.size();
	}
}

void Solver::addToClauses(CRef cr, bool learnt) {
	if (learnt) {
		if (learnts.size() >= max_learned_clauses) {
			reduceDB();
		}
		newlearnts.insert(cr);
		learnts.push(cr);
	} else {
		newclauses.insert(cr);
		clauses.push(cr);
	}
}

/**
 * Checks whether at least one watch is a decision variable.
 * If not, it randomly chooses one and makes it a decision variable
 * This guarantees that when all decision vars have been chosen, all clauses are certainly satisfied
 *
 * complexity: O(1)
 */
void Solver::checkDecisionVars(const Clause& c) {
	if(not modes().lazy){ // Optimization // TODO invars should guarantee this (and speedup in other case?)
		MAssert((not isFalse(c[0]) && isDecisionVar(var(c[0]))) || (not isFalse(c[1]) && isDecisionVar(var(c[1]))));
		return;
	}
	MAssert(not isFalse(c[0]) || not isFalse(c[1]));
	if (isFalse(c[0])) {
		setDecidable(var(c[1]), true);
	} else if (isFalse(c[1])) {
		setDecidable(var(c[0]), true);
	} else if (not isDecisionVar(var(c[0])) && not isDecisionVar(var(c[1]))) {
		auto choice = irand(random_seed, 2);
		MAssert(choice==0 || choice==1);
		setDecidable(var(c[choice]), true);
	}
	MAssert((not isFalse(c[0]) && isDecisionVar(var(c[0]))) || (not isFalse(c[1]) && isDecisionVar(var(c[1]))));
}

void Solver::detachClause(CRef cr, bool strict) {
	auto& c = ca[cr];
	MAssert(c.size() > 1);

	if (strict) {
		remove(watches[~c[0]], Watcher(cr, c[1]));
		remove(watches[~c[1]], Watcher(cr, c[0]));
	} else {
		// Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
		watches.smudge(~c[0]);
		watches.smudge(~c[1]);
	}

	if (c.learnt()) {
		learnts_literals -= c.size();
	} else {
		clauses_literals -= c.size();
	}
}

// Store the entailed literals and save all new clauses, both in learnts and clauses
// NOTE: never call directly from within!
void Solver::saveState() {
	// Reset stored info
	if (trail_lim.size() > 0) {
		roottraillim = trail_lim[0];
	} else {
		roottraillim = trail.size();
	}
	newclauses.clear();
	newlearnts.clear();
	savedrootlits.clear();

	savedok = ok;
	remove_satisfied = false;
}

void Solver::removeUndefs(std::set<CRef>& newclauses, vec<CRef>& clauses) {
	int i, j;
	for (i = j = 0; i < clauses.size(); i++) {
		if (newclauses.find(clauses[i]) != newclauses.cend()) {
			removeClause(clauses[i]);
		} else {
			clauses[j++] = clauses[i];
		}
	}
	clauses.shrinkByNb(i - j);
	newclauses.clear();
}

// Reset always backtracks to 0 if there are new entailed literals
// NOTE: never call directly from within!
void Solver::resetState() {
	if (verbosity > 3) {
		clog << ">>> Resetting the state.\n";
	}
	ok = savedok;
	auto newtrailrootlim = trail.size();
	if (trail_lim.size() > 0) {
		newtrailrootlim = trail_lim[0];
	}
	if (roottraillim != (uint) newtrailrootlim) {
		trail_lim[0] = roottraillim;
		uncheckedBacktrack(0);
	}
	removeUndefs(newclauses, clauses);
	removeUndefs(newlearnts, learnts);

	for(auto i=rootunitlits.begin(); i!=rootunitlits.end();){
		if(savedrootlits.find(*i)!=savedrootlits.cend()){
			i = rootunitlits.erase(i);
		}else{
			++i;
		}
	}

	remove_satisfied = true;
}

void Solver::removeClause(CRef cr) {
	auto& c = ca[cr];
	detachClause(cr);
	// Don't leave pointers to free'd memory!
	if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
	c.mark(1);
	ca.free(cr);
}

bool Solver::satisfied(const Clause& c) const {
	for (int i = 0; i < c.size(); i++) {
		if (value(c[i]) == l_True) return true;
	}
	return false;
}

// BACKTRACKING

void Solver::uncheckedBacktrack(int level) {
	if (verbosity > 8) {
		clog << "Backtracking to " << level << "\n";
	}
	auto levelatstart = decisionLevel();
	Lit decision = trail[trail_lim[level]];
	for (int c = trail.size() - 1; c >= trail_lim[level]; c--) {
		Var x = var(trail[c]);
		assigns[x] = l_Undef;
		if (phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last())){
			polarity[x] = sign(trail[c]);
		}
		insertVarOrder(x);
	}
	qhead = trail_lim[level];
	trail.shrinkByNb(trail.size() - trail_lim[level]);
	int levels = trail_lim.size() - level;
	trail_lim.shrinkByNb(levels);
	if (levelatstart > level) {
		getPCSolver().backtrackDecisionLevel(level, decision);
	}
	backtracked = true;
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
void Solver::cancelUntil(int level) {
	if (decisionLevel() > level) {
		uncheckedBacktrack(level);
	}
}

// VARIABLE CHOICE

Lit Solver::pickBranchLit() {
	Var next = var_Undef;

	// Random decision:
	if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
		next = order_heap[irand(random_seed, order_heap.size())];
		if (value(mkPosLit(next)) == l_Undef && decision[next]) {
			rnd_decisions++;
		}
	}

	// Activity based decision:
	bool start = true;
	while (next == var_Undef || value(mkPosLit(next)) != l_Undef || !decision[next]) {
		if (!start) { // So then remove it if it proved redundant
			order_heap.removeMin();
		}
		start = false;

		if (order_heap.empty()) {
			next = var_Undef;
			break;
		} else {
			//next = order_heap.removeMin(); //REMOVES the next choice from the heap
			next = order_heap.peek(); //Does NOT remove this
		}
	}

	if (!start && next != var_Undef) {
		order_heap.removeMin();
	}

	// Choose polarity based on different polarity modes (global or per-variable):
	if (next == var_Undef) {
		return lit_Undef;
	} else if (user_pol[next] != l_Undef) {
		return mkLit(next, user_pol[next] == l_True);
	} else if (rnd_pol) {
		return mkLit(next, drand(random_seed) < 0.5);
	} else {
		return mkLit(next, polarity[next]);
	}
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
 |      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
 |        rest of literals. There may be others from the same level though.
 |
 |________________________________________________________________________________________________@*/
bool Solver::isAlreadyUsedInAnalyze(const Lit& lit) const {
	return seen[var(lit)] == 1;
}

void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel) {
	int pathC = 0;
	Lit p = lit_Undef;

	/*AB VERY IMPORTANT*/
	int lvl = 0;
	auto& c = ca[confl];
	for (int i = 0; i < c.size(); i++) {
		int litlevel = getLevel(var(c[i]));
		if (litlevel > lvl) {
			lvl = litlevel;
		}
	}

	MAssert(lvl<=decisionLevel());

	cancelUntil(lvl);

	MAssert(confl!=CRef_Undef);
	MAssert(lvl==decisionLevel());
	/*AE*/

	// Generate conflict clause:
	//
	out_learnt.push(); // (leave room for the asserting literal)
	int index = trail.size() - 1;

	if(verbosity>4){
		clog <<"Conflict found, creating learned clause at decision level " <<decisionLevel() <<".\n";
	}

	/*A*/
	bool deleteImplicitClause = false;
	do {
		MAssert(confl != CRef_Undef);
		// (otherwise should be UIP)
		auto& c = ca[confl];

		/*AB*/
		if (verbosity > 6) {
			clog << "\tCurrent conflict clause: ";
			printClause(confl);
			clog << "\n";
			clog << "\tCurrent learned clause: ";
			for (int i = 1; i < out_learnt.size(); i++) {
				clog << toString(out_learnt[i]) << " ";
			}
			clog << "\n";
		}
		/*AE*/

		if (c.learnt()) claBumpActivity(c);

		for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
			Lit q = c[j];

			if (!seen[var(q)] && getLevel(var(q)) > 0) {
				varBumpActivity(var(q));
				seen[var(q)] = 1;
				if (getLevel(var(q)) >= decisionLevel())
					pathC++;
				else
					out_learnt.push(q);
			}
		}

		/*AB*/

		if (deleteImplicitClause) {
			ca.free(confl);
			deleteImplicitClause = false;
		}
		/*AE*/

		// Select next clause to look at:
		while (!seen[var(trail[index--])])
			;
		p = trail[index + 1];
		confl = reason(var(p));

		/*AB*/
		if (verbosity > 6) {
			clog << "\tGetting explanation for " << toString(p) << "\n";
		}

		if (confl == CRef_Undef && pathC > 1) {
			confl = getPCSolver().getExplanation(p);
			deleteImplicitClause = true;
		}
		if (verbosity > 6 && confl != CRef_Undef) {
			clog << "\tExplanation is ";
			printClause(confl);
			clog << "\n";
		}
		/*AE*/

		seen[var(p)] = 0;
		pathC--;

	} while (pathC > 0);
	out_learnt[0] = ~p;

	// Simplify conflict clause:
	//
	int i, j;
	out_learnt.copyTo(analyze_toclear);
	if (ccmin_mode == 2) {
		uint32_t abstract_level = 0;
		for (i = 1; i < out_learnt.size(); i++)
			abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

		for (i = j = 1; i < out_learnt.size(); i++)
			if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level)) out_learnt[j++] = out_learnt[i];

	} else if (ccmin_mode == 1) {
		for (i = j = 1; i < out_learnt.size(); i++) {
			Var x = var(out_learnt[i]);

			if (reason(x) == CRef_Undef)
				out_learnt[j++] = out_learnt[i];
			else {
				auto& c = ca[reason(var(out_learnt[i]))];
				for (int k = 1; k < c.size(); k++)
					if (!seen[var(c[k])] && getLevel(var(c[k])) > 0) {
						out_learnt[j++] = out_learnt[i];
						break;
					}
			}
		}
	} else
		i = j = out_learnt.size();

	max_literals += out_learnt.size();
	out_learnt.shrinkByNb(i - j);
	tot_literals += out_learnt.size();

	// Find correct backtrack level:
	//
	if (out_learnt.size() == 1)
		out_btlevel = 0;
	else {
		int max_i = 1;
		// Find the first literal assigned at the next-highest level:
		for (int i = 2; i < out_learnt.size(); i++)
			if (getLevel(var(out_learnt[i])) > getLevel(var(out_learnt[max_i]))) max_i = i;
		// Swap-in this literal at index 1:
		Lit p = out_learnt[max_i];
		out_learnt[max_i] = out_learnt[1];
		out_learnt[1] = p;
		out_btlevel = getLevel(var(p));
	}

	for (int j = 0; j < analyze_toclear.size(); j++)
		seen[var(analyze_toclear[j])] = 0; // ('seen[]' is now cleared)

	/*A*/
}

// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels) {
	analyze_stack.clear();
	analyze_stack.push(p);
	int top = analyze_toclear.size();
	while (analyze_stack.size() > 0) {
		MAssert(reason(var(analyze_stack.last())) != CRef_Undef);
		auto& c = ca[reason(var(analyze_stack.last()))];
		analyze_stack.pop();

		for (int i = 1; i < c.size(); i++) {
			Lit p = c[i];
			if (!seen[var(p)] && getLevel(var(p)) > 0) {
				if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0) {
					seen[var(p)] = 1;
					analyze_stack.push(p);
					analyze_toclear.push(p);
				} else {
					for (int j = top; j < analyze_toclear.size(); j++)
						seen[var(analyze_toclear[j])] = 0;
					analyze_toclear.shrinkByNb(analyze_toclear.size() - top);
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

	if (decisionLevel() == 0) return;

	seen[var(p)] = 1;

	for (int i = trail.size() - 1; i >= trail_lim[0]; i--) {
		Var x = var(trail[i]);
		if (seen[x]) {
			auto explan = getPCSolver().getExplanation(value(mkPosLit(x))==l_True?mkPosLit(x):mkNegLit(x));
			if (explan == CRef_Undef) {
				MAssert(getLevel(x) > 0);
				out_conflict.push(~trail[i]);
			} else {
				auto& c = ca[explan];
				for (int j = 1; j < c.size(); j++)
					if (getLevel(var(c[j])) > 0){
						seen[var(c[j])] = 1;
					}
			}
			seen[x] = 0;
		}
	}

	seen[var(p)] = 0;
}

litlist Solver::getUnsatExplanation() const{
	litlist list;
	for(int i=0; i<conflict.size(); ++i){
		list.push_back(conflict[i]);
	}
	return list;
}

void Solver::checkedEnqueue(Lit p, CRef from) {
	if (value(p) != l_True) {
		uncheckedEnqueue(p, from);
	}
}

void Solver::uncheckedEnqueue(Lit p, CRef from) {
	MAssert(value(p) == l_Undef);
	assigns[var(p)] = lbool(!sign(p));
	vardata[var(p)] = mkVarData(from, decisionLevel());
	trail.push_(p);

	if (not isDecisionVar(var(p))) {
		setDecidable(var(p), true);
	}
	getPCSolver().notifySetTrue(p);
	if (verbosity > 3) {
		getPCSolver().printEnqueued(p);
	}
}

bool Solver::isDecided(Var v) {
	if(value(mkPosLit(v))==l_Undef){
		return false;
	}
	auto level = getLevel(v);
	MAssert(level >= 0 || level <= decisionLevel());
	return var(trail[trail_lim[getLevel(v)-1]]) == v;
}

/*_________________________________________________________________________________________________
 |
 |  propagate : [void]  ->  [Clause*]
 |
 |  Description:
 |    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
 |    otherwise CRef_Undef.
 |
 |    Post-conditions:
 |      * the propagation queue is empty, even if there was a conflict.
 |________________________________________________________________________________________________@*/
CRef Solver::propagate() {
	return getPCSolver().propagate();
}

CRef Solver::notifypropagate() {
	if (backtracked) {
		auto level = decisionLevel();
		for (auto i = rootunitlits.begin(); i != rootunitlits.end();) {
			if (i->level <= (uint) level) {
				if (value(i->lit) == l_False) {
					return i->explan;
				}
				checkedEnqueue(i->lit, i->explan);
				++i;
			} else {
				i = rootunitlits.erase(i);
			}
		}
		backtracked = false;
	}
	if (decisionLevel() == 0 && needsimplify) {
		if (not simplify()) {
			return getPCSolver().createClause( { }, true);
		}
	}

	CRef confl = CRef_Undef;
	int num_props = 0;
	watches.cleanAll();

	while (qhead < trail.size()) {
		auto p = trail[qhead++]; // 'p' is enqueued fact to propagate.
		auto& ws = watches[p];
		Watcher *i, *j, *end;
		num_props++;

		for (i = j = (Watcher*) ws, end = i + ws.size(); i != end;) {
			// Try to avoid inspecting the clause:
			Lit blocker = i->blocker;
			if (value(blocker) == l_True) {
				if(modes().lazy){ // TODO guarantee non-lazy decision invar here again!
					setDecidable(var(blocker), true);
				}
				*j++ = *i++;
				continue;
			}

			// Make sure the false literal is data[1]:
			CRef cr = i->cref;
			auto& c = ca[cr];
			MAssert(isDecisionVar(var(c[0])) || isDecisionVar(var(c[1])));
			Lit false_lit = ~p;
			if (c[0] == false_lit) {
				c[0] = c[1], c[1] = false_lit;
			}
			MAssert(c[1] == false_lit);
			i++;

			// If 0th watch is true, then clause is already satisfied.
			Lit first = c[0];
			Watcher w = Watcher(cr, first);
			if (first != blocker && value(first) == l_True) {
				*j++ = w;
				/*A*/
				checkDecisionVars(c);
				continue;
			}

			// Look for new watch:
			for (int k = 2; k < c.size(); k++) {
				if (value(c[k]) != l_False) {
					c[1] = c[k];
					c[k] = false_lit;
					watches[~c[1]].push(w);
					/*A*/
					checkDecisionVars(c);
					goto NextClause;
				}
			}

			// Did not find watch -- clause is unit under assignment:
			*j++ = w;
			if (value(first) == l_False) { // NOTE: conflict during unit propagation
				confl = cr;
				qhead = trail.size();
				// Copy the remaining watches: (NOTE: will cause loop to be false)
				while (i < end) {
					*j++ = *i++;
				}
			} else {
				uncheckedEnqueue(first, cr);
				/*A*/checkDecisionVars(c);
			}

			NextClause: ;
		}
		ws.shrinkByNb(i - j);
		if (confl != CRef_Undef) {
			qhead = trail.size();
		}
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
	ClauseAllocator& ca;
	reduceDB_lt(ClauseAllocator& ca_) :
			ca(ca_) {
	}
	bool operator ()(CRef x, CRef y) {
		return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
	}
};
void Solver::reduceDB() {
	int i, j;
	double extra_lim = cla_inc / learnts.size(); // Remove any clause below this activity

	sort(learnts, reduceDB_lt(ca));
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++) {
		auto& c = ca[learnts[i]];
		if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
			removeClause(learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	learnts.shrinkByNb(i - j);
	checkGarbage();
}

void Solver::removeSatisfied(vec<CRef>& cs) {
	int i, j;
	for (i = j = 0; i < cs.size(); i++) {
		auto& c = ca[cs[i]];
		if (satisfied(c)) {
			removeClause(cs[i]);
		} else {
			cs[j++] = cs[i];
		}
	}
	cs.shrinkByNb(i - j);
}

void Solver::rebuildOrderHeap() {
	vec<Var> vs;
	for (Var v = 0; v < nVars(); v++) {
		if (decision[v] && value(mkPosLit(v)) == l_Undef) vs.push(v);
	}
	order_heap.build(vs);
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
	needsimplify = false;
	MAssert(decisionLevel() == 0);

	if (!ok || propagate() != CRef_Undef) return ok = false;

	if (nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;

	// Remove satisfied clauses:
	removeSatisfied(learnts);
	if (remove_satisfied) { // Can be turned off.
		removeSatisfied(clauses);
	}
	checkGarbage();
	rebuildOrderHeap();

	simpDB_assigns = nAssigns();
	simpDB_props = clauses_literals + learnts_literals; // (shouldn't depend on stats really, but it will do for now)

	return true;
}

/*_________________________________________________________________________________________________
 |
 |  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
 |
 |  Description:
 |    Search for a model the specified number of conflicts.
 |    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
 |
 |  Output:
 |    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
 |    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
 |    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
 |________________________________________________________________________________________________@*/
lbool Solver::search(int maxconflicts, bool nosearch/*AE*/) {
	MAssert(ok);
	int backtrack_level;
	int conflictC = 0;
	vec<Lit> learnt_clause;
	starts++;
	needsimplify = true;

	auto confl = nullPtrClause;
	for (;;) {
		if (getPCSolver().terminateRequested()) {
			return l_Undef;
		}
		if (not ok) {
			return l_False;
		}
		if (confl == nullPtrClause) { // NOTE: otherwise, a conflict was found during the final check.
			confl = propagate();
		}
		if (not ok) {
			return l_False;
		}

		if (confl != CRef_Undef) {
			// CONFLICT
			conflicts++;
			conflictC++;
			if (decisionLevel() == 0) {
				return l_False;
			}

			learnt_clause.clear();

			analyze(confl, learnt_clause, backtrack_level);

			cancelUntil(backtrack_level);

			auto cr = CRef_Undef;
			if (learnt_clause.size() > 1) {
				cr = ca.alloc(learnt_clause, true);
				addToClauses(cr, true);
				attachClause(cr);
				claBumpActivity(ca[cr]);
			}
			uncheckedEnqueue(learnt_clause[0], cr);

			varDecayActivity();
			claDecayActivity();

			if (--learntsize_adjust_cnt == 0) {
				learntsize_adjust_confl *= learntsize_adjust_inc;
				learntsize_adjust_cnt = (int) learntsize_adjust_confl;
				max_learnts *= learntsize_inc;

				if (verbosity >= 1) {
					fprintf(stderr, "| %9d | %7d %8d %8d | %8d %8d %6.0f |\n", (int) conflicts,
							(int) dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int) clauses_literals,
							(int) max_learnts, nLearnts(), (double) learnts_literals / nLearnts());
				}
			}

		} else {
			// NO CONFLICT
			if ((maxconflicts >= 0 && conflictC >= maxconflicts)) {
				// Reached bound on number of conflicts:
				cancelUntil(0);
				return l_Undef;
			}

			// Simplify the set of problem clauses:
			if (decisionLevel() == 0 && not simplify()) {
				return l_False;
			}

			if (learnts.size() - nAssigns() >= max_learnts) {
				// Reduce the set of learnt clauses:
				reduceDB();
			}

			Lit next = lit_Undef;
			while (decisionLevel() < assumptions.size()) {
				//clog <<"Assumption\n";
				// Perform user provided assumption:
				Lit p = assumptions[decisionLevel()];
				if (value(p) == l_True) {
					// Dummy decision level:
					createNewDecisionLevel();
				} else if (value(p) == l_False) {
					analyzeFinal(~p, conflict);
					return l_False;
				} else {
					next = p;
					break;
				}
			}

			if (next == lit_Undef) {
				if (nosearch) {
					return l_True;
				}

				// New variable decision:
				decisions++;
				next = pickBranchLit();

				if (next == lit_Undef) {
					confl = getPCSolver().notifyFullAssignmentFound();
					if (confl != nullPtrClause) {
						continue;
					}
					return l_True;
				}
			}

			if (verbosity > 3) {
				getPCSolver().printChoiceMade(decisionLevel() + 1, next);
			}

			// Increase decision level and enqueue 'next'
			createNewDecisionLevel();
			uncheckedEnqueue(next);
		}
		confl = CRef_Undef;
	}
	return l_Undef; // Note: is (should be anyway) unreachable but not detected by compiler
}

/*
 Finite subsequences of the Luby-sequence:

 0: 1
 1: 1 1 2
 2: 1 1 2 1 1 2 4
 3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
 ...


 */

static double luby(double y, int x) {
	// Find the finite subsequence that contains index 'x', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1)
		;

	while (size - 1 != x) {
		size = (size - 1) >> 1;
		seq--;
		x = x % size;
	}

	return pow(y, seq);
}

void Solver::setAssumptions(const litlist& assumps) {
	// Note: important: when setting to identical assumptions, no action should be taken!!! (important for CORRECTNESS of finding multiple optim models)
	bool identical = true;
	if((int)assumps.size()!=assumptions.size()){
		identical = false;
	}
	for(uint i=0; i<assumps.size() && identical; ++i){
		if(assumps[i]!=assumptions[i]){
			identical = false;
		}
	}
	if(identical){
		return;
	}

	if (oneshot) {
		MAssert(not assumpset);
	}
	if (not oneshot && assumpset) {
		getPCSolver().resetState();
	}
	cancelUntil(0);
	assumptions.clear();
	//clog <<"Assumptions: ";
	for (auto i = assumps.cbegin(); i < assumps.cend(); ++i) {
		assumptions.push(*i);
		//clog <<toString(*i) <<" ";
	}
	//clog <<"\n";
	if (not oneshot) {
		getPCSolver().saveState();
	}
	assumpset = true;
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve(bool nosearch) {
	if (not assumpset) {
		getPCSolver().saveState(); // NOTE: to assure that the state has been saved exactly once
	}
	assumpset = true;

	model.clear();
	conflict.clear();
	if (!ok) {
		return l_False;
	}

	// To get a better estimate of the number of max_learnts allowed, have to ask all propagators their size
	max_learnts = getPCSolver().getNbOfFormulas() * learntsize_factor;
	learntsize_adjust_confl = learntsize_adjust_start_confl;
	learntsize_adjust_cnt = (int) learntsize_adjust_confl;
	auto status = l_Undef;

	// Search:
	int curr_restarts = 0;
	while (status == l_Undef) {
		if (getPCSolver().terminateRequested()) {
			return l_Undef;
		}
		double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
		status = search(rest_base * restart_first/*AB*/, nosearch/*AE*/);
		if (getPCSolver().terminateRequested()) {
			return l_Undef;
		}
		if (nosearch) {
			return status;
		}
		curr_restarts++;
	}

	if (status == l_True) {
		// Extend & copy model:
		model.growTo(nVars());
		for (int i = 0; i < nVars(); i++) {
			model[i] = value(mkPosLit(i));
		}
#ifndef NDEBUG
		for(int i=0; i<nbClauses(); ++i) {
			auto c = getClause(i);
			bool clausetrue = false, clauseHasNonFalseDecidable = false;
			for(int j=0; j<getClauseSize(c); ++j) {
				if(not isFalse(getClauseLit(c, j)) && isDecisionVar(var(getClauseLit(c, j)))) {
					clauseHasNonFalseDecidable = true;
				}
				if(isTrue(getClauseLit(c, j))) {
					clausetrue = true;
				}
			}
			if(not clausetrue || not clauseHasNonFalseDecidable) {
				clog <<(clausetrue?"True":"False") <<", " <<(clauseHasNonFalseDecidable?"decidable":"undecidable") <<" clause ";
				printClause(c);
			}
			MAssert(clausetrue && clauseHasNonFalseDecidable);
		}
#endif
	} else if (status == l_False && conflict.size() == 0) {
		ok = false;
	}

	return status;
}

void Solver::printClause(CRef rc) const {
	const auto& c = ca[rc];
	bool begin = true;
	for (int i = 0; i < c.size(); i++) {
		if (not begin) {
			clog << " | ";
		}
		begin = false;
		clog << toString(c[i]);
	}
	clog << "\n";
}

//=================================================================================================
// Garbage Collection methods:
void Solver::relocAll(ClauseAllocator& to) {
	// All watchers:
	//
	// for (int i = 0; i < watches.size(); i++)
	watches.cleanAll();
	for (int v = 0; v < nVars(); v++)
		for (int s = 0; s < 2; s++) {
			Lit p = mkLit(v, s);
			// printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
			vec<Watcher>& ws = watches[p];
			for (int j = 0; j < ws.size(); j++)
				ca.reloc(ws[j].cref, to);
		}

	// All reasons:
	//
	for (int i = 0; i < trail.size(); i++) {
		Var v = var(trail[i]);

		if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))) ca.reloc(vardata[v].reason, to);
	}

	// All learnt:
	//
	for (int i = 0; i < learnts.size(); i++)
		ca.reloc(learnts[i], to);

	// All original:
	//
	for (int i = 0; i < clauses.size(); i++)
		ca.reloc(clauses[i], to);
}

void Solver::garbageCollect() {
	// Initialize the next region to a size corresponding to the estimated utilization degree. This
	// is not precise but should avoid some unnecessary reallocations for the new region:
	ClauseAllocator to(ca.size() - ca.wasted());

	relocAll(to);
	if (verbosity >= 2) {
		fprintf(stderr, "|  Garbage collection:   %12d bytes => %12d bytes             |\n", ca.size() * ClauseAllocator::Unit_Size,
				to.size() * ClauseAllocator::Unit_Size);
	}
	to.moveTo(ca);
}

void Solver::printStatistics() const {
	std::clog << "> restarts              : " << starts << "\n";
	std::clog << "> conflicts             : " << decisions << "  (" << (float) rnd_decisions * 100 / (float) decisions << " % random)\n";
	std::clog << "> decisions             : " << starts << "\n";
	std::clog << "> propagations          : " << propagations << "\n";
	std::clog << "> conflict literals     : " << tot_literals << "  (" << ((max_literals - tot_literals) * 100 / (double) max_literals)
			<< " % deleted)\n";
}

int Solver::printECNF(std::ostream& stream, std::set<Var>& printedvars) {
	if (not okay()) {
		stream << "0\n";
		return 0;
	}
	for (int i = 0; i < clauses.size(); ++i) {
		const auto& clause = ca[clauses[i]];
		stringstream ss;
		auto clausetrue = false;
		for (int j = 0; not clausetrue && j < clause.size(); ++j) {
			Lit lit = clause[j];
			lbool val = value(lit);
			if (val == l_Undef) {
				ss << (sign(lit) ? -(var(lit) + 1) : var(lit) + 1) << " ";
				printedvars.insert(var(lit));
			} else if (val == l_True) {
				clausetrue = true;
			}
		}
		if (not clausetrue) {
			ss << "0\n";
			stream << ss.str();
		}
	}

	// Print implied literals
	int lastrootassertion = trail.size();
	if (trail_lim.size() > 0) {
		lastrootassertion = trail_lim[0];
	}
	for (int i = 0; i < lastrootassertion; ++i) {
		Lit lit = trail[i];
		stream << (sign(lit) ? -(var(lit) + 1) : var(lit) + 1) << " 0\n";
	}

	return clauses.size() + lastrootassertion;
}

void Solver::accept(ConstraintVisitor& visitor){
	if(isUnsat()){
		visitor.add(Disjunction({mkPosLit(1)}));
		visitor.add(Disjunction({mkNegLit(1)}));
		return;
	}
	for(int i=0; i<trail.size(); ++i){
		visitor.add(Disjunction({trail[i]}));
	}
	acceptClauseList(visitor, clauses);
	acceptClauseList(visitor, learnts);
}

void Solver::acceptClauseList(ConstraintVisitor& visitor, const vec<CRef>& list){
	for(int i=0; i<list.size(); ++i){
		Disjunction d;
		auto& c = ca[list[i]];
		bool istrue = false;
		for(auto j=0; j<c.size() && not istrue; j++){
			if(value(c[j])==l_True){
				istrue = true;
			}
			d.literals.push_back(c[j]);
		}
		if(not istrue){
			visitor.add(d);
		}
	}
}
