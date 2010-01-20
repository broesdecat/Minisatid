#ifndef IDSOLVER_H_
#define IDSOLVER_H_

#include <cstdio>
#include <set>
#include <stack>
#include <queue>
#include <vector>
#include <map>

#include "Vec.h"
#include "Queue.h"
#include "Heap.h"
#include "Alg.h"

#include "SolverTypes.h"
#include "Solver.h"
#include "AggSolver.h"

/**
 * The different possible typs of definitions.
 * If a variable is NONDEFALL, no definition is associated with it.
 * If a variable is NONDEFPOS, a definition is associated with it, but there is no recursion through it in the POSITIVE dependency graph
 * 		but there might be recursion over negation (relevant for the well-founded model)
 */
enum DefType	{NONDEFTYPE, DISJ, CONJ, AGGR};
enum DefOcc		{NONDEFOCC, POSLOOP, MIXEDLOOP, BOTHLOOP};
enum UFS 		{NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK};

enum FINDCS			{ always, adaptive, lazy};
enum MARKDEPTH		{ include_cs, stop_at_cs};
enum SEARCHSTRAT	{ breadth_first, depth_first};

class Solver;
class AggSolver;

class Rule {
private:
    vec<Lit> lits;

public:
    const Var head;

    Rule(vec<Lit>& ps, bool conj): head(var(ps[0])){
    	for(int i=1; i<ps.size(); i++){
    		lits.push(ps[i]);
    	}
    }

    int 	size() 	const	{ return lits.size(); }
    Lit 	getHeadLiteral() 	const	{ return Lit(head, false); }
    Lit 	operator [](int i) 	const	{ return lits[i]; }
};

class IDSolver{
public:
	IDSolver();
	virtual ~IDSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify	();
	void 	backtrack 	( Lit l);
	Clause* getExplanation	(Lit p);    // Create a clause that implicitly was the reason for p's propagation.
	void 	notifyVarAdded	(); 		//correctly initialized TSolver datastructures when vars are added
	Clause* propagateDefinitions();
	Clause* propagate(Lit p);
	//void Subsetminimize(const vec<Lit>& lits);

	bool 	isWellFoundedModel();
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////AGGSOLVER NECESSARY
	vec<bool>	isCS;                   		// Per atom: is it a cycle source?

	vec<Lit>&	getCFJustificationAggr	(Var v);
	void 		cycleSourceAggr			(Var v, vec<Lit>& nj, bool becamecyclesource);
	void 		notifyAggrHead			(Var head);
	/////////////////////END AGGSOLVER NECESSARY

	/////////////////////INITIALIZATION
	void    	addRule      				(bool conj, vec<Lit>& ps);	// Add a rule to the solver.
	bool    	finishECNF_DataStructures 	();							// Initialize the ECNF data structures. NOTE: aggregates may set the "ok" value to false!

	void setSolver(Solver* s){
		solver = s;
	}

	void setAggSolver(AggSolver* s){
		aggsolver = s;
	}

	int	verbosity;          // Verbosity level. 0=silent, 1=some progress report
	FINDCS		defn_strategy;      // Controls which propagation strategy will be used for definitions.                         (default always)
	MARKDEPTH	defn_search;        // Controls which search type will be used for definitions.                                  (default include_cs)
	SEARCHSTRAT	ufs_strategy;		//Which algorithm to use to find unfounded sets
	/////////////////////END INITIALIZATION

protected:
	bool 		init;
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
	vec<Var>		defdVars;	// All the vars that are the head of some kind of definition (disj, conj or aggr). Allows to iterate over all definitions.
	vec<Rule*>		definition;	// If defType[v]==DISJ or CONJ, definition[v] is the 'long clause' of the completion of v's rule.
	// Note that v occurs negatively if DISJ, positively if CONJ; and the reverse for the body literals.
	// NOTE: If defType[v]==NONDEF, it may be that v is defined, but that no positive loop can exist. It SHOULD NOT be deleted then
	//		because it will be used for WELLFOUNDED model checking later on.
	//	of the completion of that rule, which was just not deleted, but wont be used any more
	vec<DefType>	defType;	// Gives the type of definition for each VAR
	vec<DefOcc>		defOcc;	// Gives the type of definition occurence for each VAR
	vec<int>		scc;		// To which strongly connected component does the atom belong. Zero iff defType[v]==NONDEF.
	bool 			posloops, negloops;

	DefType 	getDefType(Var v);
	bool		isDefInPosGraph(Var v);
	bool		isDefined(Var v);
	bool 		isConjunctive(Var v);
	bool 		isDisjunctive(Var v);
	bool		setTypeIfNoPosLoops(Var v);

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
	void	apply_changes      ();                                // Copy sp_justification to cf_justification.
	void	clear_changes      ();                                // Restore sp_justification to the state of cf_justification.
	void	change_jstfc_disj  (Var v, Lit j);                    // Change sp_justification of DISJ atom v to j.
	void	change_jstfc_aggr  (Var v, const vec<Lit>& j);        // Change sp_justification of AGGR atom v to j.

	// Cycle source methods:
	void	addCycleSource		(Var v);
	void	clearCycleSources	();
	void	findCycleSources	();                                // Starting from cf_justification, creates a supporting justification in sp_justification, and records the changed atoms in 'cycle sources'.
	void	justify				(Var v);


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

	UFS 	visitForUFSsimple	(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& visited, vec<vec<Lit> >& network);
	void 	changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& visited); //changes the justifications of the tarjan algorithm

	bool	visitedEarlierTarjan(Var x, Var y, vec<Var>& visitedandjust);
	bool	visitedTarjan(Var x, vec<Var>& visitedandjust);
	int		visitedAtTarjan(Var x, vec<Var>& visitedandjust);
	bool	hasJustificationTarjan(Var x, vec<Var>& visitedandjust);

	void	markNonJustified   			(Var cs, vec<Var>& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	void	markNonJustifiedAddParents	(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	bool	directlyJustifiable			(Var v, std::set<Var>& ufs, Queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified					(Lit x);
	bool	isJustified					(Var x);
	bool	propagateJustified			(Var v, Var cs, std::set<Var>& ufs, Queue<Var>& q);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified
	Clause* addLoopfClause				(Lit l, vec<Lit>& lits);

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter); // Method to initialize 'scc'.
	void visitFull(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter, bool throughPositiveLit, vec<int>& rootofmixed, vec<Var>& nodeinmixed);

	// Debug:
	void     printLit         (Lit l);
	template<class C>
	void     printClause      (const C& c);
	void     printRule        (const Rule& c);
	void     checkLiteralCount();
	bool     isCycleFree      ();			// Verifies whether cf_justification is indeed cycle free, not used, for debugging purposes.

	void 	addExternalDisjuncts(const std::set<Var>& ufs, vec<Lit>& loopf);

	inline bool isPositive(Lit l);
	inline bool isTrue(Lit l);
	inline bool isFalse(Lit l);
	inline bool isUnknown(Lit l);
	inline bool isTrue(Var l);
	inline bool isFalse(Var l);
	inline bool isUnknown(Var l);
	inline bool canBecomeTrue(Lit l);
	inline bool inSameSCC(Var x, Var y);
	inline Lit 	createNegativeLiteral(Var x);
	inline Lit 	createPositiveLiteral(Var x);

	/*******************************
	 * WELL FOUNDED MODEL CHECKING *
	 *******************************/

private:
    stack<int> wfstack;          //!< Stack for Tarjan's algorithm.
    /*    - _visited[v] == 0  \f$ \Rightarrow \f$ v is not visited yet.
     *    - _visited[v] > 0   \f$ \Rightarrow \f$ v is visited, but not yet in a component.
     *    - _visited[v] == -1 \f$ \Rightarrow \f$ v is in a component.
     */
    vector<int> wfvisited;
    vector<Var> wfroot;				//!< Root vector for Tarjan's algorithm.
    vector<Var> wfmixedCycleRoots;	//!< To store one literal for each mixed cycle in the justification graph.
    vector<int> wfcounters;
    int 		wfvisitNr;			//!< Counter for Tarjan's algorithm.

    set<Var> 		wfmarkedAtoms;	//!< The set of all literals that are marked.
    vector<bool> 	wfisMarked;		//!< Vector to check whether an atom is marked (still unknown).
    queue<Lit> 		wfqueuePropagate;
    bool 			wffixpoint;

	/*!
	 * \brief Implementation of Tarjan's algorithm for detecting strongly connected components.
	 */
	void visitWF(Var, bool);
	/*!
	 * \brief Search for mixed cycles in the justification graph of the current model.
	 *
	 * \post For every mixed cycle in the justification graph, there is one literal of the cycle on \c _mixedCycleRoots.
	 *
	 * Main structure of findMixedCycles():
	 * \code
	 *    for( //each defined, true literal litp with non empty body )
	 *       Visit(litp);
	 * \endcode
	 */
	void findMixedCycles();
	/*!
	 * \brief Mark all atoms that are above the mixed cycle roots in the justification graph.
	 *
	 * Main structure of markUpward()
	 * \code
	 *    \\ mark all cycle roots.
	 *    \\ mark all literals that are above the cycle roots.
	 * \endcode
	 */
	void markUpward();
	/*!
	 * \brief Mark a literal.
	 */
	void mark(Var);
	/*!
	 * \brief For marked literal l, set _counters[l] to the number of marked bodyliterals in its body. When l is conj/disj, and contains an false/true unmarked bodyliteral, l is pushed on _queuePropagate.
	 */
	void initializeCounters();
	void forwardPropagate(bool);
	void overestimateCounters();
	void removeMarks();
};


//=================================================================================================
// Implementation of inline methods:

inline void	IDSolver::addCycleSource(Var v)		{ if (!isCS[v]) {isCS[v]=true; css.push(v);} }
inline void	IDSolver::clearCycleSources()		{ for (int i=0;i<css.size();i++) isCS[css[i]]=false; css.clear(); }

inline bool IDSolver::isPositive(Lit l)			{ return !sign(l); }
inline bool IDSolver::isTrue(Lit l)				{ return value(l)==l_True; }
inline bool IDSolver::isTrue(Var v)				{ return value(v)==l_True; }
inline bool IDSolver::isFalse(Lit l)			{ return value(l)==l_False; }
inline bool IDSolver::isFalse(Var v)			{ return value(v)==l_False; }
inline bool IDSolver::isUnknown(Lit l)			{ return value(l)==l_Undef; }
inline bool IDSolver::isUnknown(Var v)			{ return value(v)==l_Undef; }
inline bool IDSolver::canBecomeTrue(Lit l)		{ return value(l)!=l_False; }
inline bool IDSolver::inSameSCC(Var x, Var y) 	{ return scc[x] == scc[y] && scc[x]!=-1; }	//-1 indicates not defined
inline Lit 	IDSolver::createNegativeLiteral(Var i)	{ return Lit(i, true); }
inline Lit 	IDSolver::createPositiveLiteral(Var i)	{ return Lit(i, false); }

inline DefType IDSolver::getDefType(Var v)		{ return defType[v]; }
inline bool IDSolver::isDefInPosGraph(Var v)	{ return defOcc[v]==POSLOOP || defOcc[v]==BOTHLOOP; }
inline bool	IDSolver::isDefined(Var v)			{ return defOcc[v]!=NONDEFOCC; }
inline bool IDSolver::isConjunctive(Var v)		{ return getDefType(v)==CONJ; }
inline bool IDSolver::isDisjunctive(Var v)		{ return getDefType(v)==DISJ; }

/**
 * All these methods are used to allow branch prediction in SATsolver methods and to minimize the number of
 * subsequent calls
 */

inline Clause* IDSolver::propagate(Lit p){
	return NULL;
}

//only call this when the whole queue has been propagated
inline Clause* IDSolver::propagateDefinitions(){
	if (init || !posloops) {return NULL;}
	return indirectPropagate();
}

inline void IDSolver::backtrack ( Lit l){
	return;
}

inline Clause* IDSolver::getExplanation	(Lit p){
	assert(false);
}

#endif /* IDSOLVER_H_ */
