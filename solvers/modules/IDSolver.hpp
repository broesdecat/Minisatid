//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
Copyright (c) 2006-2009, Maarten Mariën

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
#ifndef IDSOLVER_H_
#define IDSOLVER_H_

#include <cstdio>
#include <set>
#include <stack>
#include <queue>
#include <vector>
#include <map>

#include "solvers/utils/Utils.hpp"
#include "solvers/modules/DPLLTmodule.hpp"

namespace MinisatID {

class PCSolver;
class AggSolver;

/**
 * The different possible types of definitions.
 * If a variable is NONDEFALL, no definition is associated with it.
 * If a variable is NONDEFPOS, a definition is associated with it, but there is no recursion through it in the POSITIVE dependency graph
 * 		but there might be recursion over negation (relevant for the well-founded model)
 */
enum DefType	{ NONDEFTYPE = 0, WASDEFDISJ = 1, WASDEFCONJ = 2, WASDEFAGGR = 3, DISJ = 4, CONJ = 5, AGGR=6 };
enum DefOcc 	{ NONDEFOCC, POSLOOP, MIXEDLOOP, BOTHLOOP };
enum UFS 		{ NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK };

class PropRule {
private:
    vec<Lit> lits;

public:
    const Var head;

    PropRule(Lit head, const vec<Lit>& ps): head(var(head)){
    	for(int i=0; i<ps.size(); i++){
    		lits.push(ps[i]);
    	}
    }

    int 	size() 				const	{ return lits.size(); }
    Lit 	getHeadLiteral() 	const	{ return mkLit(head, false); }
    Lit 	operator [](int i) 	const	{ return lits[i]; }
};

class IDSolver: public DPLLTmodule{
private:
	MinisatID::AggSolver*		aggsolver;
	long			unfoundedsets;
	int				previoustrailatsimp; //The size of the trail the previous time simplification was run.

public:
	IDSolver(MinisatID::PCSolver* s);
	virtual ~IDSolver();

	MinisatID::AggSolver*	getAggSolver()const{return aggsolver;}
	void		setAggSolver(MinisatID::AggSolver* a){aggsolver = a;}

	/////////////////////SOLVER NECESSARY
	void 		backtrack 				(const Lit& l);
	void 		notifyVarAdded			(int nvars); 		//correctly initialized TSolver datastructures when vars are added
	rClause 	propagateDefinitions	();
	rClause 	propagate				(const Lit&);

	bool 		isWellFoundedModel		();

	std::vector<std::vector<Lit> > reasons;	// std::map vars to vec<Lit> which were the reason of deriving it
	rClause 	getExplanation			(const Lit& p);    // Create a clause that implicitly was the reason for p's propagation.

	/////////////////////ENDSOLVER NECESSARY

	/////////////////////AGGSOLVER NECESSARY
	const vec<Lit>&	getCFJustificationAggr	(Var v) const;
	void 			cycleSourceAggr			(Var v, vec<Lit>& nj);
	void 			notifyAggrHead			(Var head);
	void 			removeAggrHead			(Var head);
	/////////////////////END AGGSOLVER NECESSARY

	/////////////////////INITIALIZATION
	bool    	addRule      			(bool conj, Lit head, const vec<Lit>& ps);	// Add a rule to the solver.
	bool    	finishECNF_DataStructures();							// Initialize the ECNF data structures. NOTE: aggregates may set the "ok" value to false!
	/////////////////////END INITIALIZATION

	PropRule const* const	getDefinition(Var head) const { assert(definition[head]!=NULL); return definition[head]; }
	DefType 	getDefType			(Var i) const { return defType[i]; }
	bool		isDefined			(Var v) const; //Whether the variable is currently the head of any definition
	bool 		originallyDefined	(Var v) const; //Whether the variable has been the head of a definition at any point during execution
	bool 		isConjunctive		(Var v) const;
	bool 		isDisjunctive		(Var v) const;
	bool		isDefinedByAggr		(Var v) const;

	//False if problem unsat
	bool 		initAfterSimplify	();

	void		printStatistics		() const;

	void 		newDecisionLevel();

protected:
	void			setDefinition(Var head, PropRule* r) { definition[head]=r; }

	std::vector<PropRule*>	definition;	// If defType[v]==DISJ or CONJ, definition[v] is the 'long clause' of the completion of v's rule.
	// Note that v occurs negatively if DISJ, positively if CONJ; and the reverse for the body literals.
	// NOTE: If defType[v]==NONDEF, it may be that v is defined, but that no positive loop can exist. It SHOULD NOT be deleted then
	//		because it will be used for WELLFOUNDED model checking later on.
	std::vector<DefType>	defType;	// Gives the type of definition for each VAR
	std::vector<DefOcc>	defOcc;		// Gives the type of definition occurrence for each VAR

	bool 		recagg;	//true if recursive aggregates are present
	vec<bool>	isCS;                   // Per atom: is it a cycle source?
	vec<int>	seen, seen2;

	bool 		firstsearch;
	uint64_t 	prev_conflicts/*not strictly a statistic!*/;
    uint64_t 	cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts;
    uint64_t 	nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;

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
	std::vector<Var>		defdVars;	// All the vars that are the head of some kind of definition (disj, conj or aggr). Allows to iterate over all definitions.
	vec<int>		scc;		// To which strongly connected component does the atom belong. Zero iff defType[v]==NONDEF.
	bool 			posloops, negloops;

	std::set<Var>		toremoveaggrheads; //The set of defined aggregates that are no longer defined and should be removed from IDSolver during simplification.

	bool		isDefInPosGraph		(Var v) const;
	bool		setTypeIfNoPosLoops	(Var v) const;

	void 		propagateJustificationDisj(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads);
	void 		propagateJustificationAggr(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads);
	void 		propagateJustificationConj(Lit l, vec<Lit>& heads);

	void 		findJustificationDisj(Var v, vec<Lit>& jstf);
	bool 		findJustificationDisj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	bool 		findJustificationConj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	bool 		findJustificationAggr(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);

	// Rules (body to head):
	std::vector<std::vector<Var> >	disj_occurs;         // Per literal: a std::vector of heads of DISJ rules in which it is a body literal.
	std::vector<std::vector<Var> >	conj_occurs;         // Per literal: a std::vector of heads of CONJ rules in which it is a body literal.

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
	void 	checkJustification			(Var head);

	// Propagation method:
	rClause  indirectPropagate  		();                        /* Main method.
                                                                      1) Finds cycle sources and supporting justification.
                                                                      2) Applies 'unfounded(..)' on each of them,
                                                                      3) ... asserting an unfounded set as soon as one is found, or
                                                                         applying the changes to 'J' after no unfounded set is found for any cycle source.
	 */

	// Auxiliary for indirectPropagate:
	bool	indirectPropagateNow();                               // Decide (depending on chosen strategy) whether or not to do propagations now.
	bool	unfounded          (Var cs, std::set<Var>& ufs);      // True iff 'cs' is currently in an unfounded set, 'ufs'.
	rClause	assertUnfoundedSet (const std::set<Var>& ufs);

//	UFS 	visitForUFSgeneral	(Var v, Var cs, std::set<Var>& ufs, int visittime, vec<Var>& stack, vec<Var>& root, vec<Var>& visited, vec<bool>& incomp);
	UFS 	visitForUFSsimple	(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& visited, vec<vec<Lit> >& network);
	void 	changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& visited); //changes the justifications of the tarjan algorithm

	bool	visitedEarlierTarjan	(Var x, Var y, const vec<Var>& visitedandjust)	const;
	bool	visitedTarjan			(Var x, const vec<Var>& visitedandjust) 		const;
	int		visitedAtTarjan			(Var x, const vec<Var>& visitedandjust) 		const;
	bool	hasJustificationTarjan	(Var x, const vec<Var>& visitedandjust)			const;

	void	markNonJustified   			(Var cs, vec<Var>& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Var v, Var cs, std::queue<Var> &q, vec<Var>& tmpseen);
	void	markNonJustifiedAddParents	(Var x, Var cs, std::queue<Var> &q, vec<Var>& tmpseen);
	bool	directlyJustifiable			(Var v, std::set<Var>& ufs, std::queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified					(Lit x) const;
	bool	isJustified					(Var x) const;
	bool	propagateJustified			(Var v, Var cs, std::set<Var>& ufs);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified
	void	addLoopfClause				(Lit l, vec<Lit>& lits);

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter); // Method to initialize 'scc'.
	void visitFull(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter, bool throughPositiveLit, vec<int>& rootofmixed, vec<Var>& nodeinmixed);

	// Debug:
	void	print		(const rClause c)	const;
	void	print		(const PropRule& c)		const;
	bool	isCycleFree	() 					const;			// Verifies whether justification is indeed cycle free, not used, for debugging purposes.

	void	addExternalDisjuncts(const std::set<Var>& ufs, vec<Lit>& loopf);

	inline bool canBecomeTrue			(Lit l) const;
	inline bool inSameSCC				(Var x, Var y) const;

	/*******************************
	 * WELL FOUNDED MODEL CHECKING *
	 *******************************/

private:
	std::vector<Var> wfroot;
	std::queue<Lit> wfqueue;
	std::set<Var> wfmarkedAtoms;
	std::vector<bool> wfisMarked;
	std::vector<Var> wfrootnodes;
	bool wffixpoint;

	/*
	 * Implementation of Tarjan's algorithm for detecting strongly connected components.
	 */
	void visitWF(Var i, std::vector<Var> &root, std::vector<bool> &incomp, std::stack<Var> &stack, std::vector<Var> &visited, int& counter, bool throughPositiveLit, std::vector<int>& rootofmixed);
	/*
	 * Search for mixed cycles in the justification graph of the current model.
	 * @post For every mixed cycle in the justification graph, there is one literal of the cycle on \c _mixedCycleRoots.
	 */
	void findMixedCycles(std::vector<Var> &root, std::vector<int>& rootofmixed);
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

/**
 * All these methods are used to allow branch prediction in SATsolver methods and to minimize the number of
 * subsequent calls
 */

/**
 * Returns non-owning pointer
 */
inline rClause IDSolver::propagate(const Lit& p){
	return nullPtrClause;
}

//only call this when the whole queue has been propagated
/**
 * Returns non-owning pointer
 */
inline rClause IDSolver::propagateDefinitions(){
	if (!isInitialized()/* || !posloops*/) {return nullPtrClause;}
	return indirectPropagate();
}

/*inline void IDSolver::backtrack( const Lit& l){
	return;
}*/

/*inline rClause IDSolver::getExplanation(const Lit& p){
	assert(false);
	return nullPtrClause;
}*/

}

#endif /* IDSOLVER_H_ */
