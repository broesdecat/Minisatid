/****************************************************************************************[Solver.h]
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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "utils/Options.h"
#include "SolverTypes.hpp"

#include <vector>
#include <iostream>
#include <set>
#include <list>
#include <map>
#include "modules/DPLLTmodule.hpp"
#include "external/MAssert.hpp"

namespace MinisatID {
class PCSolver;
class ConstraintVisitor;
}

namespace Minisat {

class Solver: public MinisatID::Propagator {
	// FIXME returning CRefs is dangerous, as they can be relocated by garbage control!
public:
	double random_var_freq;
	double random_seed;
	int verbosity;
	double var_decay;
	bool rnd_pol; // Use random polarities for branching heuristics.
	int max_learned_clauses;
	bool oneshot, assumpset;

	void setInitialPolarity(Var var, bool pol) {
		polarity[var] = pol;
	}

private:
	bool needsimplify;

	/*
	 * Reverse trail:
	 * 		after backtrack to level x, on unit-propagate, propagate all literals of which the level (2nd param) is lower or equal to x
	 * 				drop the others
	 */
	bool backtracked;
	struct ReverseTrailElem {
		Lit lit;
		uint level;
		CRef explan;

		ReverseTrailElem(Lit lit, uint level, CRef explan)
				: lit(lit), level(level), explan(explan) {
			MAssert(explan!=CRef_Undef);
		}

		bool operator<(const ReverseTrailElem& elem) const{
			return lit<elem.lit || (lit==elem.lit && level<elem.level) || (lit==elem.lit && level==elem.level && explan<elem.explan);
		}
	};
	std::list<ReverseTrailElem> rootunitlits;
	std::set<ReverseTrailElem> savedrootlits;
	void addRootUnitLit(const ReverseTrailElem& elem);

	void removeClause(CRef cr); // Detach and free a clause.
	void checkedEnqueue(Lit p, CRef from = CRef_Undef); // Enqueue a literal if it is not already true
public:
	CRef reason(Var x) const;

	bool isUnsat() const {
		return not ok;
	}
	void notifyUnsat() {
		ok = false;
	}
	int printECNF(std::ostream& stream, std::set<Var>& printedvars); // Returns the number of clauses that were added

private:
	void removeUndefs(std::set<CRef>& newclauses, vec<CRef>& clauses);
	bool addClause_(vec<Lit>& ps);
public:
	void saveState();
	void resetState();
	void printClause(const CRef c) const;

	int getNbOfAssumptions() const { return assumptions.size(); }

	CRef makeClause(const std::vector<Lit>& lits, bool learnt);
	bool addClause(const std::vector<Lit>& ps); // Add a clause to the solver.
	void addLearnedClause(CRef c); // don't check anything, just add it to the clauses and bump activity

	CRef getClause(int i) const {
		return clauses[i];
	}
	int nbClauses() const {
		return clauses.size();
	}
	int getClauseSize(CRef cr) const {
		return ca[cr].size();
	}
	Lit getClauseLit(CRef cr, int i) const {
		MAssert(0<=i && i<getClauseSize(cr));
		return ca[cr][i];
	}

	void cancelUntil(int level); // Backtrack until a certain level.
	void uncheckedBacktrack(int level); // Dangerous! Backtracks to level, without printing info or checking where we are at the moment!

	void uncheckedEnqueue(Lit p, CRef from = CRef_Undef); // Enqueue a literal. Assumes value of literal is undefined
	std::vector<Lit> getDecisions() const;
	int decisionLevel() const; // Gives the current decisionlevel.
	const vec<Lit>& getTrail() const {
		return trail;
	}
	int getTrailSize() const {
		return trail.size();
	}
	const Lit& getTrailElem(int index) const {
		return trail[index];
	}
	int getStartLastLevel() const {
		return trail_lim.size() == 0 ? 0 : trail_lim.last();
	}
	void varBumpActivity(Var v); // Increase a variable with the current 'bump' value.
	void varReduceActivity(Var v);

	uint64_t nbVars() const; // The current number of variables.

	bool isDecisionVar(Var v) const {
		MAssert(v<decision.size());
		return decision[v];
	}
	void setDecidable(Var v, bool decide);

	bool isAlreadyUsedInAnalyze(const Lit& lit) const;

	std::vector<Lit> getUnsatExplanation() const;

	//PROPAGATOR CODE
	// TODO split up in search and propagator
	virtual void accept(MinisatID::ConstraintVisitor& visitor);
private:
	void acceptClauseList(MinisatID::ConstraintVisitor& visitor, const vec<CRef>& list);
public:
	CRef getExplanation(const Lit& l) {
		return reason(var(l));
	}
	void notifyBacktrack(int untillevel, const Lit& decision) {
		Propagator::notifyBacktrack(untillevel, decision);
	}
	CRef notifypropagate();
	void printStatistics() const;
	int			getNbOfFormulas		() 				const 	{ return nClauses(); }

	virtual void notifyNewDecisionLevel() {
	}
	virtual CRef notifyFullAssignmentFound() {
		throw MinisatID::idpexception("Invalid operation on propagator.");
	}

	bool isDecided(Var v);

	int getLevel(Var x) const;

	Solver(MinisatID::PCSolver* s, bool oneshot);
	virtual ~Solver();

	// NOTE: SHOULD ONLY BE CALLED BY PCSOLVER::CREATEVAR
	Var newVar(lbool upol = l_Undef, bool dvar = true); // Add a new variable with parameters specifying variable mode.

	void setAssumptions(const std::vector<Lit>& assumps);
	lbool solve(bool nosearch = false); // Search for a model that respects a given set of assumptions.

private:
	bool simplify(); // Removes already satisfied clauses.
	bool okay() const; // FALSE means solver is in a conflicting state

public:
	// Read state:
	//
	lbool value(Lit p) const; // The current value of a literal.
	lbool rootValue(Lit p) const;
	lbool modelValue(Lit p) const; // The value of a literal in the last model. The last call to solve must have been satisfiable.
	int nAssigns() const; // The current number of assigned literals.
	int nClauses() const; // The current number of original clauses.
	int nLearnts() const; // The current number of learnt clauses.
	int nVars() const; // The current number of variables.
	int nFreeVars() const;
private:
	// Memory managment:
	virtual void garbageCollect();
	void checkGarbage(double gf);
	void checkGarbage();

	// Extra results: (read-only member variable)
	vec<lbool> model; // If problem is satisfiable, this vector contains the model (if any).
	vec<Lit> conflict; // If problem is unsatisfiable (possibly under assumptions),
					   // this vector represent the final conflict clause expressed in the assumptions.

					   // Mode of operation:
	double clause_decay;
	bool luby_restart;
	int ccmin_mode; // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
	int phase_saving; // Controls the level of phase saving (0=none, 1=limited, 2=full).
	bool rnd_init_act; // Initialize variable activities with a small random value.
	double garbage_frac; // The fraction of wasted memory allowed before a garbage collection is triggered.

	int restart_first; // The initial restart limit.                                                                (default 100)
	double restart_inc; // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
	double learntsize_factor; // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
	double learntsize_inc; // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

	int learntsize_adjust_start_confl;
	double learntsize_adjust_inc;

	// Statistics: (read-only member variable)
	uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
	uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

protected:
	void varDecayActivity(); // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
	void claDecayActivity(); // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.

	void addToClauses(CRef cr, bool learnt);

	// Helper structures:
	struct VarData {
		CRef reason;
		int level;
	};
	static inline VarData mkVarData(CRef cr, int l) {
		VarData d = { cr, l };
		return d;
	}

	struct Watcher {
		CRef cref;
		Lit blocker;
		Watcher(CRef cr, Lit p)
				: cref(cr), blocker(p) {
		}
		bool operator==(const Watcher& w) const {
			return cref == w.cref;
		}
		bool operator!=(const Watcher& w) const {
			return cref != w.cref;
		}
	};

	struct WatcherDeleted {
		const ClauseAllocator& ca;
		WatcherDeleted(const ClauseAllocator& _ca)
				: ca(_ca) {
		}
		bool operator()(const Watcher& w) const {
			return ca[w.cref].mark() == 1;
		}
	};

	struct VarOrderLt {
		const vec<double>& activity;
		bool operator ()(Var x, Var y) const {
			return activity[x] > activity[y];
		}
		VarOrderLt(const vec<double>& act)
				: activity(act) {
		}
	};

	// Solver state
	bool ok; // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
	vec<CRef> clauses; // List of problem clauses.
	vec<CRef> learnts; // List of learnt clauses.

	double cla_inc; // Amount to bump next clause with.
	vec<double> activity; // A heuristic measurement of the activity of a variable.
	double var_inc; // Amount to bump next variable with.
	OccLists<Lit, vec<Watcher>, WatcherDeleted> watches; // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
	vec<lbool> assigns; // The current assignments.
	vec<char> polarity; // The preferred polarity of each variable.
	vec<lbool> user_pol; // The users preferred polarity of each variable.
	vec<char> decision; // Declares if a variable is eligible for selection in the decision heuristic.
	vec<Lit> trail; // Assignment stack; stores all assigments made in the order they were made.
	vec<int> trail_lim; // Separator indices for different decision levels in 'trail'.
	vec<VarData> vardata; // Stores reason and level for each variable.
	int qhead; // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
	int simpDB_assigns; // Number of top-level assignments since last execution of 'simplify()'.
	int64_t simpDB_props; // Remaining number of propagations that must be made before next execution of 'simplify()'.
	vec<Lit> assumptions; // Current set of assumptions provided to solve by the user.
	Heap<VarOrderLt> order_heap; // A priority queue of variables ordered with respect to the variable activity.
	bool remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

	ClauseAllocator ca;

	// Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
	// used, exept 'seen' wich is used in several places.
	//
	vec<char> seen;
	vec<Lit> analyze_stack;
	vec<Lit> analyze_toclear;
	vec<Lit> add_tmp;

	double max_learnts;
	double learntsize_adjust_confl;
	int learntsize_adjust_cnt;

	// State saving
	bool savedok;
	std::set<CRef> newclauses, newlearnts;
	uint roottraillim;

	void insertVarOrder(Var x); // Insert a variable in the decision order priority queue.
	Lit pickBranchLit(); // Return the next decision variable.
	void createNewDecisionLevel(); // Begins a new decision level.
	bool enqueue(Lit p, CRef from = CRef_Undef); // Test if fact 'p' contradicts current state, enqueue otherwise.
	CRef propagate(); // Perform unit propagation. Returns possibly conflicting clause.
	void analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
	void analyzeFinal(Lit p, vec<Lit>& out_conflict); // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
	bool litRedundant(Lit p, uint32_t abstract_levels); // (helper method for 'analyze()')
	lbool search(int maxconcflicts, bool nosearch);
	void reduceDB(); // Reduce the set of learnt clauses.
	void removeSatisfied(vec<CRef>& cs); // Shrink 'cs' to contain only non-satisfied clauses.
	void rebuildOrderHeap();

	// Maintaining Variable/Clause activity
	void varBumpActivity(Var v, double inc); // Increase a variable with the current 'bump' value.
	void claBumpActivity(Clause& c); // Increase a clause with the current 'bump' value.

	// Operations on clauses
	void attachClause(CRef cr); // Attach a clause to watcher lists.
	void detachClause(CRef cr, bool strict = false); // Detach a clause to watcher lists.
	bool locked(const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
	bool satisfied(const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

	void relocAll(ClauseAllocator& to);

	// Misc
	uint32_t abstractLevel(Var x) const; // Used to represent an abstraction of sets of decision levels.

	void checkDecisionVars(const Clause& c);

	// Static helpers

	// Returns a random float 0 <= x < 1. Seed must never be 0.
	static inline double drand(double& seed) {
		seed *= 1389796;
		int q = (int) (seed / 2147483647);
		seed -= (double) q * 2147483647;
		return seed / 2147483647;
	}

	// Returns a random integer 0 <= x < size. Seed must never be 0.
	static inline int irand(double& seed, int size) {
		return (int) (drand(seed) * size);
	}
};

//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason(Var x) const {
	return vardata[x].reason;
}
inline int Solver::getLevel(Var x) const {
	return vardata[x].level;
}

inline void Solver::insertVarOrder(Var x) {
	if (!order_heap.inHeap(x) && decision[x])
		order_heap.insert(x);
}

inline void Solver::varDecayActivity() {
	var_inc *= (1 / var_decay);
}
inline void Solver::varBumpActivity(Var v) {
	varBumpActivity(v, var_inc);
}
inline void Solver::varReduceActivity(Var v) {
	varBumpActivity(v, -var_inc);
}
inline void Solver::varBumpActivity(Var v, double inc) {
	if ((activity[v] += inc) > 1e100) {
		// Rescale:
		for (int i = 0; i < nVars(); i++)
			activity[i] *= 1e-100;
		var_inc *= 1e-100;
	}

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.decrease(v);
}

inline void Solver::claDecayActivity() {
	cla_inc *= (1 / clause_decay);
}
inline void Solver::claBumpActivity(Clause& c) {
	if ((c.activity() += cla_inc) > 1e20) {
		// Rescale:
		for (int i = 0; i < learnts.size(); i++)
			ca[learnts[i]].activity() *= 1e-20;
		cla_inc *= 1e-20;
	}
}

inline void Solver::checkGarbage(void) {
	return checkGarbage(garbage_frac);
}
inline void Solver::checkGarbage(double gf) {
	if (ca.wasted() > ca.size() * gf)
		garbageCollect();
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool Solver::enqueue(Lit p, CRef from) {
	return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true);
}
inline bool Solver::locked(const Clause& c) const {
	return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c;
}

inline int Solver::decisionLevel() const {
	return trail_lim.size();
}
inline uint32_t Solver::abstractLevel(Var x) const {
	return 1 << (getLevel(x) & 31);
}
inline lbool Solver::value(Lit p) const {
	return assigns[var(p)] ^ sign(p);
}
inline lbool Solver::rootValue(Lit p) const {
	if (getLevel(var(p)) == 0) {
		return value(p);
	} else {
		return l_Undef;
	}
}
inline lbool Solver::modelValue(Lit p) const {
	return model[var(p)] ^ sign(p);
}
inline int Solver::nAssigns() const {
	return trail.size();
}
inline int Solver::nClauses() const {
	return clauses.size();
}
inline int Solver::nLearnts() const {
	return learnts.size();
}
inline int Solver::nVars() const {
	return vardata.size();
}
inline int Solver::nFreeVars() const {
	return (int) dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]);
}
inline bool Solver::okay() const {
	return ok;
}

inline uint64_t Solver::nbVars() const {
	return (uint64_t) nVars();
}
}

#endif
