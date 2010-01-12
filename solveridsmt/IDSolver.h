#ifndef IDSOLVER_H_
#define IDSOLVER_H_

#include <cstdio>
#include <set>
#include <map>

#include "Vec.h"
#include "Queue.h"
#include "Heap.h"
#include "Alg.h"

#include "SolverTypes.h"
#include "Solver.h"
#include "AggSolver.h"

enum DefType {NONDEF, DISJ, CONJ, AGGR};
enum UFS {NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK};

class Solver;
class AggSolver;

class IDSolver{
public:
	IDSolver();
	virtual ~IDSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify	();
	void 	backtrack 	( Lit l);
	Clause* getExplanation	(Lit p);    // Create a clause that implicitly was the reason for p's propagation.
	void 	notifyVarAdded	(); 		//correctly initialized TSolver datastructures when vars are added
	Clause* 	propagate		(Lit p, Clause* confl);
	Clause* 	propagateDefinitions(Clause* confl);
	//void Subsetminimize(const vec<Lit>& lits);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////AGGSOLVER NECESSARY
	vec<Lit>&	getCFJustificationAggr(Var v);
	vec<bool>	isCS;                   		// Per atom: is it a cycle source?
	void 		cycleSource(Var v, vec<Lit>& nj, bool becamecyclesource);
	/////////////////////END AGGSOLVER NECESSARY

	/////////////////////INITIALIZATION
	void    addRule      (bool conj, vec<Lit>& ps);          // Add a rule to the solver.
	void    finishECNF_DataStructures ();                          // Initialize the ECNF data structures. NOTE: aggregates may set the "ok" value to false!

	void setSolver(Solver* s){
		solver = s;
	}

	void setAggSolver(AggSolver* s){
		aggsolver = s;
	}

	int	verbosity;          // Verbosity level. 0=silent, 1=some progress report
	int	defn_strategy;      // Controls which propagation strategy will be used for definitions.                         (default always)
	int	defn_search;        // Controls which search type will be used for definitions.                                  (default include_cs)
	int	ufs_strategy;		//Which algorithm to use to find unfounded sets

	enum { always = 0, adaptive = 1, lazy = 2 };
	enum { include_cs = 0, stop_at_cs = 1 };
	enum { breadth_first = 0, depth_first = 1 };
	/////////////////////END INITIALIZATION

protected:
	bool init;

	vec<int>	seen, seen2;

	lbool	value(Var x) const;
	lbool	value(Lit p) const;
	int		nVars()      const;

	int64_t prev_conflicts/*not strictly a statistic!*/;

	// Statistics: (read-only member variable)
	//
	uint64_t atoms_in_pos_loops;
	//uint64_t cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts;
	//uint64_t nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;
	//    uint64_t fw_propagation_attempts, fw_propagations;

	Solver* 		solver;
	AggSolver* 		aggsolver;

	// ECNF_mode.mnmz additions to Solver state:
	vec<Lit>		to_minimize;

	// ECNF_mode.def additions to Solver state:
	//
	vec<Var>		defdVars;	// May include variables that get marked NONDEF later.
	vec<DefType>	defType;	// Per atom: what type is it (non-defined, disjunctive, conjunctive, aggregate).
	vec<Clause*>	definition;	// If defType[v]==DISJ or CONJ, definition[v] is the 'long clause' of the completion of v's rule.
	// Note that v occurs negatively if DISJ, positively if CONJ; and the reverse for the body literals.
	// If defType[v]==NONDEF, it may be that v *was* defined by a non-recursive rule: then definition[v] also is the 'long clause'
	//	of the completion of that rule, which was just not deleted, but wont be used any more
	vec<int>		scc;		// To which strongly connected component does the atom belong. Zero iff defType[v]==NONDEF.

	// Rules (body to head):
	vec<vec<Var> >  disj_occurs;         // Per literal: a vector of heads of DISJ rules in which it is a body literal.
	vec<vec<Var> >  conj_occurs;         // Per literal: a vector of heads of CONJ rules in which it is a body literal.

	// Justifications:
	vec<Lit>        cf_justification_disj;	// Per atom. cf_ = cycle free, sp_ = supporting.
	vec<Lit>        sp_justification_disj;	// _aggr. = only for AGGR atoms, _disj. = only for DISJ atoms.
	vec<vec<Lit> >  sp_justification_aggr;
	vec<vec<Lit> >  cf_justification_aggr;
	vec<Var>        changed_vars;			// A list of the atoms whose sp_ and cf_ justification are different.

	int       adaption_total;     // Used only if defn_strategy==adaptive. Number of decision levels between indirectPropagate() uses.
	int       adaption_current;   // Used only if defn_strategy==adaptive. Number of decision levels left until next indirectPropagate() use.

	// Cycle sources:
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

	//UFS 	visitForUFSgeneral	(Var v, Var cs, std::set<Var>& ufs, int visittime, vec<Var>& stack, vec<Var>& root, vec<Var>& visited, vec<bool>& incomp);

	UFS 	visitForUFSsimple	(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& visited, vec<vec<Lit> >& network, vec<Var>& tempseen);
	void 	changeJustifications(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& visited); //changes the justifications of the tarjan algorithm

	bool	visitedEarlier(Var x, Var y, vec<Var>& visitedandjust);
	bool	visited(Var x, vec<Var>& visitedandjust);
	int		visitedAt(Var x, vec<Var>& visitedandjust);
	bool	hasJustification(Var x, vec<Var>& visitedandjust);

	void	markNonJustified   	(Var cs, vec<Var>& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	void	markNonJustifiedAddParents	(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	bool	directlyJustifiable	(Var v, std::set<Var>& ufs, Queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified			(Var x);
	bool	isPositiveBodyL		(Lit x);
	bool	Justify            	(Var v, Var cs, std::set<Var>& ufs, Queue<Var>& q);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter); // Method to initialize 'scc'.

	// Debug:
	void     printLit         (Lit l);
	template<class C>
	void     printClause      (const C& c);
	//void     printRule        (const Rule& c);
	void     checkLiteralCount();
	bool     isCycleFree      ();			// Verifies whether cf_justification is indeed cycle free, not used, for debugging purposes.

	void 	createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf);
};


//=================================================================================================
// Implementation of inline methods:

inline void     IDSolver::addCycleSource(Var v)        { if (!isCS[v]) {isCS[v]=true; css.push(v);} }
inline void     IDSolver::clearCycleSources()          { for (int i=0;i<css.size();i++) isCS[css[i]]=false; css.clear(); }

/**
 * All these methods are used to allow branch prediction in SATsolver methods and to minimize the number of
 * subsequent calls
 */

inline Clause* IDSolver::propagate(Lit p, Clause* confl){
	return confl;
}

//only call this when the whole queue has been propagated
inline Clause* IDSolver::propagateDefinitions(Clause* confl){
	if (init || confl!=NULL) {return confl;}
	return indirectPropagate();
}

inline void IDSolver::backtrack ( Lit l){
	return;
}

inline Clause* IDSolver::getExplanation	(Lit p){
	return NULL;
}

#endif /* IDSOLVER_H_ */
