#ifndef IDSOLVER_H_
#define IDSOLVER_H_

#include <cstdio>
#include <set>
#include <stack>
#include <queue>
#include <vector>
#include <map>

#include "Utils.h"

#include "Vec.h"
#include "Queue.h"
#include "Heap.h"

#include "solverfwd.h"

#include "PCSolver.h"
class PCSolver;
typedef PCSolver* pPCSolver;

#include "AggSolver.h"
class AggSolver;
typedef AggSolver* pAggSolver;

class IDSolver;
typedef IDSolver* pIDSolver;


class Rule {
private:
    vec<Lit> lits;

public:
    const Var head;

    Rule(const vec<Lit>& ps): head(var(ps[0])){
    	for(int i=1; i<ps.size(); i++){
    		lits.push(ps[i]);
    	}
    }

    int 	size() 				const	{ return lits.size(); }
    Lit 	getHeadLiteral() 	const	{ return Lit(head, false); }
    Lit 	operator [](int i) 	const	{ return lits[i]; }
};

class IDSolver{
private:
	pPCSolver 		solver;
	pAggSolver		aggsolver;

public:
	IDSolver(pPCSolver s);
	virtual ~IDSolver();

	pAggSolver	getAggSolver()const{return aggsolver;}
	void		setAggSolver(pAggSolver a){aggsolver = a;}	//TODO call this

	/////////////////////SOLVER NECESSARY
	bool 		simplify				();
	void 		backtrack 				(const Lit& l);
	Clause* 	getExplanation			(const Lit& p);    // Create a clause that implicitly was the reason for p's propagation.
	void 		notifyVarAdded			(int nvars); 		//correctly initialized TSolver datastructures when vars are added
	Clause* 	propagateDefinitions	();
	Clause* 	propagate				(const Lit&);

	bool 		isWellFoundedModel		();
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////AGGSOLVER NECESSARY
	const vec<Lit>&	getCFJustificationAggr	(Var v) const;
	void 			cycleSourceAggr			(Var v, vec<Lit>& nj);
	void 			notifyAggrHead			(Var head);
	void 			removeAggrHead			(Var head);
	/////////////////////END AGGSOLVER NECESSARY

	/////////////////////INITIALIZATION
	bool    	addRule      			(bool conj, vec<Lit>& ps);	// Add a rule to the solver.
	bool    	finishECNF_DataStructures();							// Initialize the ECNF data structures. NOTE: aggregates may set the "ok" value to false!

	pPCSolver 	getSolver				()	const		{ return solver; }
	void 		remove					();			//remove this idsolver from the solver network
	/////////////////////END INITIALIZATION

	vector<Rule*>	definition;	// If defType[v]==DISJ or CONJ, definition[v] is the 'long clause' of the completion of v's rule.
	// Note that v occurs negatively if DISJ, positively if CONJ; and the reverse for the body literals.
	// NOTE: If defType[v]==NONDEF, it may be that v is defined, but that no positive loop can exist. It SHOULD NOT be deleted then
	//		because it will be used for WELLFOUNDED model checking later on.
	//	of the completion of that rule, which was just not deleted, but wont be used any more
	//	OWNER
	vec<DefType>	defType;	// Gives the type of definition for each VAR

protected:
	bool 		recagg;	//true if recursive aggregates are present
	vec<bool>	isCS;                   // Per atom: is it a cycle source?
	bool 		init;
	vec<int>	seen, seen2;

	lbool		value(Var x) const;
	lbool		value(Lit p) const;
	int			nVars()      const;

	bool 		firstsearch;
	uint64_t 	prev_conflicts/*not strictly a statistic!*/;

	// Statistics: (read-only member variable)
	//
	uint64_t 	atoms_in_pos_loops;
	//uint64_t cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts;
	//uint64_t nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;
	//uint64_t fw_propagation_attempts, fw_propagations;

	// ECNF_mode.mnmz additions to Solver state:
	vec<Lit>		to_minimize;

	// ECNF_mode.def additions to Solver state:
	//
	vec<Var>		defdVars;	// All the vars that are the head of some kind of definition (disj, conj or aggr). Allows to iterate over all definitions.
	vec<DefOcc>		defOcc;		// Gives the type of definition occurrence for each VAR
	vec<int>		scc;		// To which strongly connected component does the atom belong. Zero iff defType[v]==NONDEF.
	bool 			posloops, negloops;

	DefType 	getDefType			(Var v) const;
	bool		isDefInPosGraph		(Var v) const;
	bool		isDefined			(Var v) const;
	bool 		isConjunctive		(Var v) const;
	bool 		isDisjunctive		(Var v) const;
	bool		setTypeIfNoPosLoops	(Var v) const;

	void 		propagateJustificationDisj(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads);
	void 		propagateJustificationAggr(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads);
	void 		propagateJustificationConj(Lit l, vec<Lit>& heads);

	bool 		findJustificationDisj(Var v, vec<Lit>& jstf);
	bool 		findJustificationDisj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	bool 		findJustificationConj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	bool 		findJustificationAggr(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);

	// Rules (body to head):
	vector<vector<Var> >	disj_occurs;         // Per literal: a vector of heads of DISJ rules in which it is a body literal.
	vector<vector<Var> >	conj_occurs;         // Per literal: a vector of heads of CONJ rules in which it is a body literal.

	// Justifications:
	vec<vec<Lit> >			justification;	// Per atom. cf_ = cycle free, sp_ = supporting.

	int						adaption_total;     // Used only if defn_strategy==adaptive. Number of decision levels between indirectPropagate() uses.
	int						adaption_current;   // Used only if defn_strategy==adaptive. Number of decision levels left until next indirectPropagate() use.

	// Cycle sources:
	vec<Var>				css;                    // List of cycle sources. May still include atoms v that have !isCS[v].

	// Justification methods:
	void	apply_changes      ();
	void 	changejust(Var v, vec<Lit>& j);

	// Cycle source methods:
	void	addCycleSource				(Var v);
	void	clearCycleSources			();
	void	findCycleSources			();
	void	findJustification			(Var v);
	void 	handlePossibleCycleSource	(Var head);
	void 	checkJustification			(Var head);
	void 	checkJustification			(Var head, Lit lbecamefalse);

	// Propagation method:
	Clause*  indirectPropagate  		();                        /* Main method.
                                                                      1) Finds cycle sources and supporting justification.
                                                                      2) Applies 'unfounded(..)' on each of them,
                                                                      3) ... asserting an unfounded set as soon as one is found, or
                                                                         applying the changes to 'J' after no unfounded set is found for any cycle source.
	 */

	// Auxiliary for indirectPropagate:
	bool	indirectPropagateNow();                               // Decide (depending on chosen strategy) whether or not to do propagations now.
	bool	unfounded          (Var cs, std::set<Var>& ufs);      // True iff 'cs' is currently in an unfounded set, 'ufs'.
	Clause*	assertUnfoundedSet (const std::set<Var>& ufs);

//	UFS 	visitForUFSgeneral	(Var v, Var cs, std::set<Var>& ufs, int visittime, vec<Var>& stack, vec<Var>& root, vec<Var>& visited, vec<bool>& incomp);
	UFS 	visitForUFSsimple	(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& visited, vec<vec<Lit> >& network);
	void 	changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& visited); //changes the justifications of the tarjan algorithm

	bool	visitedEarlierTarjan	(Var x, Var y, const vec<Var>& visitedandjust)	const;
	bool	visitedTarjan			(Var x, const vec<Var>& visitedandjust) 		const;
	int		visitedAtTarjan			(Var x, const vec<Var>& visitedandjust) 		const;
	bool	hasJustificationTarjan	(Var x, const vec<Var>& visitedandjust)			const;

	void	markNonJustified   			(Var cs, vec<Var>& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	void	markNonJustifiedAddParents	(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen);
	bool	directlyJustifiable			(Var v, std::set<Var>& ufs, Queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified					(Lit x) const;
	bool	isJustified					(Var x) const;
	bool	propagateJustified			(Var v, Var cs, std::set<Var>& ufs);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified
	Clause* addLoopfClause				(Lit l, vec<Lit>& lits);

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter); // Method to initialize 'scc'.
	void visitFull(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter, bool throughPositiveLit, vec<int>& rootofmixed, vec<Var>& nodeinmixed);

	// Debug:
	void	print		(const Clause& c)	const;
	void	print		(const Rule& c)		const;
	bool	isCycleFree	() 					const;			// Verifies whether justification is indeed cycle free, not used, for debugging purposes.

	void	addExternalDisjuncts(const std::set<Var>& ufs, vec<Lit>& loopf);

	inline bool isPositive				(Lit l) const;
	inline bool isTrue					(Lit l) const;
	inline bool isFalse					(Lit l) const;
	inline bool isUnknown				(Lit l) const;
	inline bool isTrue					(Var l) const;
	inline bool isFalse					(Var l) const;
	inline bool isUnknown				(Var l) const;
	inline bool canBecomeTrue			(Lit l) const;
	inline bool inSameSCC				(Var x, Var y) const;
	inline Lit 	createNegativeLiteral	(Var x) const;
	inline Lit 	createPositiveLiteral	(Var x) const;

	/*******************************
	 * WELL FOUNDED MODEL CHECKING *
	 *******************************/

private:
	vector<Var> wfroot;
	queue<Lit> wfqueue;
	set<Var> wfmarkedAtoms;
	vector<bool> wfisMarked;
	vector<Var> wfrootnodes;
	bool wffixpoint;

	/*
	 * Implementation of Tarjan's algorithm for detecting strongly connected components.
	 */
	void visitWF(Var i, vector<Var> &root, vector<bool> &incomp, stack<Var> &stack, vector<Var> &visited, int& counter, bool throughPositiveLit, vector<int>& rootofmixed);
	/*
	 * Search for mixed cycles in the justification graph of the current model.
	 * @post For every mixed cycle in the justification graph, there is one literal of the cycle on \c _mixedCycleRoots.
	 */
	void findMixedCycles(vector<Var> &root, vector<int>& rootofmixed);
	/*
	 * Mark all atoms that are above the mixed cycle roots in the justification graph.
	 */
	void markUpward();
	void mark(Var);
	/*
	 * For marked literal l, set _counters[l] to the number of marked bodyliterals in its body. When l is conj/disj, and contains an false/true unmarked bodyliteral, l is pushed on _queuePropagate.
	 */
	void initializeCounters();
	void forwardPropagate(bool);
	void overestimateCounters();
	void removeMarks();
};

void print(IDSolver const * const id);

/**
 * All these methods are used to allow branch prediction in SATsolver methods and to minimize the number of
 * subsequent calls
 */

inline Clause* IDSolver::propagate(const Lit& p){
	return NULL;
}

//only call this when the whole queue has been propagated
inline Clause* IDSolver::propagateDefinitions(){
	if (init || !posloops) {return NULL;}
	return indirectPropagate();
}

inline void IDSolver::backtrack ( const Lit& l){
	return;
}

inline Clause* IDSolver::getExplanation	(const Lit& p){
	assert(false);
	return NULL;
}

#endif /* IDSOLVER_H_ */
