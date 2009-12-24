#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>

#include "Vec.h"
#include "Sort.h"
#include "Alg.h"

#include "SolverTypes.h"
#include "Solver.h"

class Solver;

/**
 */
class AggSolver{
public:
	AggSolver();
	virtual ~AggSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify		();
	void 	backtrack 		( Lit l);
	Clause* getExplanation	(Lit p);    // Create a clause that implicitly was the reason for p's propagation.
	void 	notifyVarAdded	(); 		//correctly initialize AMNSolver datastructures when vars are added
	Clause* 	propagate	(Lit p, Clause* confl);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////INITIALIZATION
	void    addSet       (int id, vec<Lit>& l, vec<int>& w);
	void    addAggrExpr  (int defn, int set_id, int min, int max, AggrType type);
	void    finishECNF_DataStructures ();       // Initialize datastructures.

	void setSolver(Solver* s){
		solver = s;
	}

	int       verbosity;          // Verbosity level. 0=silent, 1=some progress report
	/////////////////////END INITIALIZATION

protected:
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

	//maybe strange method, but allows to inline the normal backtrack method in the solver search and allows
	//branch prediction much better i think
	void 	doBacktrack(Lit l);

	Solver* solver;
	lbool	value(Var x) const;
	lbool	value(Lit p) const;
	int		nVars()      const;

	bool 	init;	//indicates whether still in initialization mode
	bool 	empty; 	//indicates no amn statements are present, so always return from T call

	// Debug:
	void     printLit         (Lit l);
	template<class C>
	void     printClause      (const C& c);
	void     printAggrSet     (const AggrSet& as);
	void     printAggrExpr    (const AggrExpr& ae, const AggrSet& as);
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
