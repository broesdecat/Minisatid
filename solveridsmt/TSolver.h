
#ifndef TSOLVER_H_
#define TSOLVER_H_

#include <cstdio>
#include <set>
#include <map>

#include "Vec.h"
#include "Queue.h"
#include "Heap.h"
#include "Alg.h"

#include "SolverTypes.h"
#include "Solver.h"

typedef char DefType;
const DefType NONDEF = 0;
const DefType DISJ   = 1;
const DefType CONJ   = 2;
const DefType AGGR   = 3;

struct ECNF_mode {
	bool init;              // True as long as we haven't finished the initialization.
	bool def,aggr,mnmz; // True for those extensions that are being used.  TODO : extra state for recursive aggregates!!

	ECNF_mode() : init(true), def(false), aggr(false), mnmz(false) {}
};

enum UFS {NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK};

class Solver;

class TSolver{
public:
	TSolver();
	virtual ~TSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify	();
	void 	backtrack 	( Lit l);
	Clause* getExplanation	(Lit p);    // Create a clause that implicitly was the reason for p's propagation.
	void 	notifyVarAdded	(); 		//correctly initialized TSolver datastructures when vars are added
	Clause* 	propagate		(Lit p, Clause* confl);
	Clause* 	propagateDefinitions(Clause* confl);
	//void Subsetminimize(const vec<Lit>& lits);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////INITIALIZATION
	bool    addRule      (bool conj, vec<Lit>& ps);          // Add a rule to the solver.
	bool    addAMO       (vec<Lit>& ps);                           // Add an At most one statement to the solver.
	void    addSet       (int id, vec<Lit>& l, vec<int>& w);
	void    addAggrExpr  (int defn, int set_id, int min, int max, AggrType type);
	void    finishECNF_DataStructures ();                          // Initialize the ECNF data structures. NOTE: aggregates may set the "ok" value to false!

	void setSolver(Solver* s){
		solver = s;
	}

	// Mode of operation:
	//
	ECNF_mode ecnf_mode;

	int	verbosity;          // Verbosity level. 0=silent, 1=some progress report
	int	defn_strategy;      // Controls which propagation strategy will be used for definitions.                         (default always)
	int	defn_search;        // Controls which search type will be used for definitions.                                  (default include_cs)
	int	ufs_strategy;		//Which algorithm to use to find unfounded sets

	enum { always = 0, adaptive = 1, lazy = 2 };
	enum { include_cs = 0, stop_at_cs = 1 };
	enum { breadth_first = 0, depth_first = 1 };
	/////////////////////END INITIALIZATION

protected:
	vec<int>	seen;
//	vec<char> 	assigns;

	lbool	value(Var x) const;
	lbool	value(Lit p) const;
	int		nVars()      const;

	// Statistics: (read-only member variable)
	//
	int64_t prev_conflicts/*not strictly a statistic!*/;
	uint64_t cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts, atoms_in_pos_loops;
	uint64_t nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;
	//    uint64_t fw_propagation_attempts, fw_propagations;

	Solver* solver;

	// ECNF_mode.mnmz additions to Solver state:
	vec<Lit>            to_minimize;

	// ECNF_mode.aggr additions to Solver state:
	//
	vec<AggrExpr*>        aggr_exprs;           // List of aggregate expressions as occurring in the problem.
	vec<AggrSet*>         aggr_sets;            // List of aggregate sets being used.
	vec<AggrReason*>      aggr_reason;          // For each atom, like 'reason'.
	vec<vec<AggrWatch> >  Aggr_watches;         // Aggr_watches[v] is a list of sets in which v occurs (each AggrWatch says: which set, what type of occurrence).
	// If defType[v]==AGGR, (Aggr_watches[v])[0] has type==DEFN and expr->c==Lit(v,false).

	// NOTE: this adds an invariant to the system: each literal with a truth value is put on the trail only once.
	Clause* Aggr_propagate        (Lit p);                      // Perform propagations from aggregate expressions.
	Clause* Aggr_propagate        (AggrSet& cs, AggrExpr& ce);  // Auxiliary for the previous.
	Clause* aggrEnqueue           (Lit p, AggrReason* cr);      // Like "enqueue", but for aggregate propagations.

	// ECNF_mode.def additions to Solver state:
	//
	vec<Var>        defdVars;            // May include variables that get marked NONDEF later.
	vec<DefType>    defType;             // Per atom: what type is it (non-defined, disjunctive, conjunctive, aggregate).
	vec<Clause*>    definition;          // If defType[v]==DISJ or CONJ, definition[v] is the 'long clause' of the completion of v's rule.
	// Note that v occurs negatively if DISJ, positively if CONJ; and the reverse for the body literals.
	// If defType[v]==NONDEF, it may be that v *was* defined by a non-recursive rule: then definition[v] also is the 'long clause' of the completion of that rule.
	vec<int>        scc;                 // To which strongly connected component does the atom belong. Zero iff defType[v]==NONDEF.

	// Rules (body to head):
	vec<vec<Var> >  disj_occurs;         // Per literal: in which DISJ rules (defining atom) it is body literal.
	vec<vec<Var> >  conj_occurs;         // Per literal: in which CONJ rules (defining atom) it is body literal.
	// cfr. Aggr_watches for the same thing in AGGR rules.

	// Justifications:
	vec<Lit>        cf_justification_disj;  // Per atom. cf_ = cycle free.
	vec<vec<Lit> >  cf_justification_aggr;  //           sp_ = supporting.
	vec<Lit>        sp_justification_disj;  //           _aggr. = only for AGGR atoms.
	vec<vec<Lit> >  sp_justification_aggr;  //           _disj. = only for DISJ atoms.
	vec<Var>        changed_vars;           // A list of the atoms whose sp_ and cf_ justification are different.

	int       adaption_total;     // Used only if defn_strategy==adaptive. Number of decision levels between indirectPropagate() uses.
	int       adaption_current;   // Used only if defn_strategy==adaptive. Number of decision levels left until next indirectPropagate() use.

	// Cycle sources:
	vec<bool>       isCS;                   // Per atom: is it a cycle source?
	vec<Var>        css;                    // List of cycle sources. May still include atoms v that have !isCS[v].

	// Justification methods:
	void     apply_changes      ();                                // Copy sp_justification to cf_justification.
	void     clear_changes      ();                                // Restore sp_justification to the state of cf_justification.
	void     change_jstfc_disj  (Var v, Lit j);                    // Change sp_justification of DISJ atom v to j.
	void     change_jstfc_aggr  (Var v, const vec<Lit>& j);        // Change sp_justification of AGGR atom v to j.

	// Cycle source methods:
	void     addCycleSource     (Var v);
	void     clearCycleSources  ();
	void     findCycleSources   ();                                // Starting from cf_justification, creates a supporting justification in sp_justification, and records the changed atoms in 'cycle sources'.
	void     findCycleSources   (Var v);                           // Auxiliary for findCycleSources(): v is non-false and its cf_justification does not support it.


	// Propagation method:
	Clause*  indirectPropagate  ();                                /* Main method.
                                                                      1) Finds cycle sources and supporting justification.
                                                                      2) Applies 'unfounded(..)' on each of them,
                                                                      3) ... asserting an unfounded set as soon as one is found, or
                                                                         applying the changes to 'J' after no unfounded set is found for any cycle source.
	 */

	// Auxiliary for indirectPropagate:
	bool	indirectPropagateNow();                               // Decide (depending on chosen strategy) whether or not to do propagations now.
	bool	unfounded          (Var cs, std::set<Var>& ufs);      // True iff 'cs' is currently in an unfounded set, 'ufs'.
	Clause*	assertUnfoundedSet (const std::set<Var>& ufs);

	UFS 	visitForUFSgeneral	(Var v, Var cs, std::set<Var>& ufs, int visittime, vec<Var>& stack, vec<Var>& root, vec<Var>& visited, vec<bool>& incomp);
	UFS 	visitForUFSsimple	(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& visited, vec<vec<Lit> >& network, vec<bool>& validjust);
	void 	changeJustifications(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<bool>& changedjust, vec<int>& visited); //changes the justifications of the tarjan algorithm

	void	markNonJustified   (Var cs, vec<Var>& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	void	markNonJustifiedAddParents(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	bool	directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	Justify            (Var v, Var cs, std::set<Var>& ufs, Queue<Var>& q);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter); // Method to initialize 'scc'.

	// Debug:
	void     printLit         (Lit l);
	template<class C>
	void     printClause      (const C& c);
	void     printRule        (const Rule& c);
	void     printAggrSet     (const AggrSet& as);
	void     printAggrExpr    (const AggrExpr& ae, const AggrSet& as);
	void     checkLiteralCount();
	bool     isCycleFree      ();                      // Verifies whether cf_justification is indeed cycle free.

	void 	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf);
};


//=================================================================================================
// Implementation of inline methods:

inline void     TSolver::addCycleSource(Var v)        { if (!isCS[v]) {isCS[v]=true; css.push(v);} }
inline void     TSolver::clearCycleSources()          { for (int i=0;i<css.size();i++) isCS[css[i]]=false; css.clear(); }

#endif /* TSOLVER_H_ */
