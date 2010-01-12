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
	Clause* propagate	(Lit p, Clause* confl);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////IDSOLVER NECESSARY
	void propagateJustifications(Var l, vec<vec<Lit> >& jstf, vec<Var>& v, vec<int> &nb_body_lits_to_justify);

	//geeft de watch terug naar het aggregaat waarvan v de head is
	AggrWatch& getWatchOfHeadOccurence(Var v);
	vec<AggrWatch>& getWatches(Var v);

	void findCycleSourcesFromBody(Lit l);
	void findCycleSourcesFromHead(Var l);

	bool directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q, vec<Lit>& j, vec<int>& seen, const vec<int>& scc);
	/////////////////////END IDSOLVER NECESSARY

	/////////////////////INITIALIZATION
	void    addSet       (int id, vec<Lit>& l, vec<int>& w);
	/**
	 * Adds an aggregate of the given type with number defn for set set_id.
	 * If lower, then AGG <= bound
	 * else 		  bound <= AGG
	 */
	void    addAggrExpr  (int defn, int set_id, int bound, bool lower, AggrType type);
	void    finishECNF_DataStructures ();       // Initialize datastructures.

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

	int 	getCurrentMinimum(vec<WLit>& lits);
	int 	getCurrentMaximum(vec<WLit>& lits);
	int 	getMinimum(vec<WLit>& lits);
	int 	getMaximum(vec<WLit>& lits);
	int 	getSum(vec<WLit>& lits);
	int 	getProduct(vec<WLit>& lits);

	Solver* solver;
	IDSolver* idsolver;

	bool 	init;	//indicates whether still in initialization mode
	bool 	empty; 	//indicates no amn statements are present, so always return from T call

	// NOTE: this adds an invariant to the system: each literal with a truth value is put on the trail only once.
	Clause* Aggr_propagate		(Lit p);		// Perform propagations from aggregate expressions.

	void 	findCycleSources	(AggrWatch& v);

	int		nVars()      const;

	// Debug:
	void     printLit         (Lit l, lbool value);
	template<class C>
	void     printClause      (const C& c);
	//void     printAggrSet     (const AggrSet& as);
	void     printAggrExpr    (const Agg& ae);
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

inline Clause* AggSolver::propagate(Lit p, Clause* confl){
	if (init || confl != NULL) {return confl;}
	return Aggr_propagate(p);
}

#endif /* AggSolver_H_ */
