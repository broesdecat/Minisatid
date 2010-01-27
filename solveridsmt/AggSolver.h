#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>

#include "Vec.h"
#include "Sort.h"

#include "Agg.h"
#include "Solver.h"
#include "IDSolver.h"

class Solver;
class IDSolver;
class Agg;

extern int verbosity;

class AggSolver{
public:
	static AggSolver* aggsolver;
	AggSolver();
	virtual ~AggSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify		();
	void 	backtrack 		( Lit l);

	/*
	 * Returns the explanation for the deduction of p from an aggregate expression.
	 * This method constructs, from the AggrReason stored for it, a "reason clause" usable in clause learning.
	 * @post the first element in the reason clause will be the literal itself (invariant by minisat!)
	 * @post the clause is not saved, so HAS to be deleted after use
	 */
	Clause* getExplanation	(Lit p);
	void 	notifyVarAdded	(); 		//correctly initialize AMNSolver datastructures when vars are added
	Clause* propagate	(Lit p);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////IDSOLVER NECESSARY
	void propagateJustifications(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, vec<int> &nb_body_lits_to_justify);

	void findCycleSourcesFromBody(Lit l);
	void findCycleSourcesFromHead(Var l);

	bool directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	void createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);

	/**
	 * Adds the heads of the aggregates in which x occurs as a body literal to heads
	 */
	void getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads);

	/**
	 * Returns the set literals of the aggregate with the given head x.
	 * TODO rewrite the code such that a reference can be returned to the vec of literals in the set
	 */
	void getLiteralsOfAggr(Var x, vec<Lit>& lits);
	/////////////////////END IDSOLVER NECESSARY

	/////////////////////INITIALIZATION
	/**
	 * Adds the set with the given id to the solver and sets its literals and its weights.
	 *
	 * @pre: no set with the same id has already been added
	 * @pre: negative weights are not allowed
	 * @pre: empty sets are not allowed
	 *
	 * @post: the literal set is sorted according to increasing weight.
	 *
	 * @remark: please ensure that all id numbers are used without gaps in the numbering.
	 */
	void    addSet       (int id, vec<Lit>& l, vec<int>& w);

	/**
	 * Adds an aggregate of the given type with number defn for set set_id.
	 * If lower, then AGGRvalue <= bound
	 * else 		  bound <= AGGRvalue
	 *
	 * Notifies the id solver that a new aggregate has been added
	 *
	 * Also adds a watch for each atom occurring in body or head. Watches are added by ATOM, not by LITERAL
	 *
	 * @pre: no weights==0 when using a product aggregate
	 */
	void    addAggrExpr  (int defn, int set_id, int bound, bool lower, AggrType type);

	/**
	 * Checks presence of aggregates and initializes all counters.
	 * @Return: true if there are aggregates present
	 */
	bool    finishECNF_DataStructures ();

	void setSolver(Solver* s){
		solver = s;
	}

	void setIDSolver(IDSolver* s){
		idsolver = s;
	}

	/////////////////////END INITIALIZATION

	//are used by agg.c, but preferably should be move into protected again
	Clause* 		notifySATsolverOfPropagation(Lit p, AggrReason* cr);	// Like "enqueue", but for aggregate propagations.
	vec<AggrSet*>	aggr_sets;      					// List of aggregate sets being used.

	// Debug:
	void     printLit        (Lit l, lbool value);
	void     printAggrExpr   (const Agg& ae);

protected:
	/**
	 * Returns the watch set on the aggregate in which the given variable is the head.
	 */
	AggrWatch& 			getWatchOfHeadOccurence	(Var v);

	// ECNF_mode.aggr additions to Solver state:
	//
	vec<Agg*>				aggr_exprs;		// List of aggregate expressions as occurring in the problem.
	vec<AggrReason*>		aggr_reason;	// For each atom, like 'reason'.
	vec<vec<AggrWatch> >	aggr_watches;	// Aggr_watches[v] is a list of sets in which VAR v occurs (each AggrWatch says: which set, what type of occurrence).
			//INVARIANT: if a literal is defined by an aggregate, the watch on the expression in which it is head
			//	will be the first element of its watches list

	/**
	 * Correct the min and max values of the aggregates in which l was propagated and delete any aggregate reasons
	 * present.
	 *
	 * @optimization possible: for each decision level, put the current values on a stack. Instead of recalculating it
	 * for each literal, pop the values once for each decision level
	 *
	 * @PRE: backtracking is in anti-chronologous order and all literals are visited!
	 */
	void 	doBacktrack(Lit l);
	void 	backtrackOnePropagation(Agg& ae, Occurrence tp, int index);

	Solver*		solver;
	IDSolver*	idsolver;

	bool		init;	//indicates whether still in initialization mode
	bool		empty; 	//indicates no amn statements are present, so always return from T call

	// NOTE: this adds an invariant to the system: each literal with a truth value is put on the trail only once.

	/**
	 * Goes through all watches and propagates the fact that p was set true.
	 */
	Clause* Aggr_propagate		(Lit p);

	void 	findCycleSources	(AggrWatch& v);

	int		nVars()      const;
};

//=======================
//INLINE METHODS
//=======================

inline void AggSolver::backtrack ( Lit l){
	if(init){
		return;
	}else{
		doBacktrack(l);
	}
}

//@pre: conflicts are empty
inline bool AggSolver::simplify(){
	return true;
}

inline Clause* AggSolver::propagate(Lit p){
	if (init) {return NULL;}
	return Aggr_propagate(p);
}

#endif /* AggSolver_H_ */
