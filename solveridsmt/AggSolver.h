#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>

#include "Vec.h"
#include "Sort.h"
#include "Alg.h"

#include "Agg.h"
#include "Solver.h"
#include "IDSolver.h"

class Solver;
class IDSolver;
class Agg;

class AggSolver{
public:
	static AggSolver* aggsolver;
	AggSolver();
	virtual ~AggSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify		();
	void 	backtrack 		( Lit l);
	Clause* getExplanation	(Lit p);    // Create a clause that implicitly was the reason for p's propagation.
	void 	notifyVarAdded	(); 		//correctly initialize AMNSolver datastructures when vars are added
	Clause* propagate	(Lit p);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////IDSOLVER NECESSARY
	void propagateJustifications(Var l, vec<vec<Lit> >& jstf, vec<Var>& v, vec<int> &nb_body_lits_to_justify);

	void findCycleSourcesFromBody(Lit l);
	void findCycleSourcesFromHead(Var l);

	bool directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc);
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
	void    addSet       (int id, vec<Lit>& l, vec<int>& w);
	/**
	 * Adds an aggregate of the given type with number defn for set set_id.
	 * If lower, then AGG <= bound
	 * else 		  bound <= AGG
	 */
	void    addAggrExpr  (int defn, int set_id, int bound, bool lower, AggrType type);
	/**
	 * Initializes data structures and checks whether there are any aggregates present.
	 * @Return: true if there are aggregates
	 */
	bool    finishECNF_DataStructures ();

	void setSolver(Solver* s){
		solver = s;
	}

	void setIDSolver(IDSolver* s){
		idsolver = s;
	}

	int	verbosity;          // Verbosity level. 0=silent, 1=some progress report
	/////////////////////END INITIALIZATION

	//are used by agg.c, but preferably should be move into protected again
	Clause* 		aggrEnqueue(Lit p, AggrReason* cr);	// Like "enqueue", but for aggregate propagations.
	vec<AggrSet*>	aggr_sets;      					// List of aggregate sets being used.

protected:
	AggrWatch& 			getWatchOfHeadOccurence	(Var v);

	// ECNF_mode.aggr additions to Solver state:
	//
	vec<Agg*>				aggr_exprs;		// List of aggregate expressions as occurring in the problem.
	vec<AggrReason*>		aggr_reason;	// For each atom, like 'reason'.
	vec<vec<AggrWatch> >	Aggr_watches;	// Aggr_watches[v] is a list of sets in which VAR v occurs (each AggrWatch says: which set, what type of occurrence).
			//INVARIANT: if a literal is defined by an aggregate, the watch on the expression in which it is head
			//	will be the first element of its watches list

	//maybe strange method, but allows to inline the normal backtrack method in the solver search and allows
	//branch prediction much better i think
	void 	doBacktrack(Lit l);
	void 	backtrackOnePropagation(Agg& ae, Occurrence tp, int index);

	Solver*		solver;
	IDSolver*	idsolver;

	bool		init;	//indicates whether still in initialization mode
	bool		empty; 	//indicates no amn statements are present, so always return from T call

	// NOTE: this adds an invariant to the system: each literal with a truth value is put on the trail only once.
	Clause* Aggr_propagate		(Lit p);		// Perform propagations from aggregate expressions.
	void 	findCycleSources	(AggrWatch& v);
	int		nVars()      const;

	// Debug:
	void     printLit        (Lit l, lbool value);
	void     printAggrExpr   (const Agg& ae);
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
