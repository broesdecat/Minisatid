#ifndef AMNSolver_H_
#define AMNSolver_H_

#include <cstdio>

#include "Vec.h"
#include "Alg.h"

#include "SolverTypes.h"
#include "Solver.h"

class Solver;

/**
 * AMNSolver is used for exists unique, at most n and at least n, because they all allow for better
 * propagation then by using the normal sum aggregate.
 */
class AMNSolver{
public:
	AMNSolver();
	virtual ~AMNSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify		();
	void 	backtrack 		( Lit l);
	void 	notifyVarAdded	(); 		//correctly initialize AMNSolver datastructures when vars are added
	Clause* 	propagate	(Lit p, Clause* confl);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////INITIALIZATION
	void    addAMN	(vec<Lit>& ps, int n = 1);  // Add an at-most-N statement to the solver.
	void    addALN	(vec<Lit>& ps, int n = 1);  // Add an at-least-N statement to the solver.
	void    addEE	(vec<Lit>& ps, int n = 1);  // Add an exist-exactly-N statement to the solver.
	void    finishECNF_DataStructures ();       // Initialize datastructures.

	void setSolver(Solver* s){
		solver = s;
	}

	int       verbosity;          // Verbosity level. 0=silent, 1=some progress report
	/////////////////////END INITIALIZATION

protected:
	Solver* solver;
	lbool	value(Var x) const;
	lbool	value(Lit p) const;
	int		nVars()      const;

	bool 	init;	//indicates whether still in initialization mode
	bool 	empty; 	//indicates no amn statements are present, so always return from T call

	vec<Clause*> amnclauses;
	vec<int> amncounter; 		//maps the clause index of an amn statement to its current counter of true elements
	vec<int> amnbound; 			//maps the clause index of an amn statement to its upper bound of true literals
	vec<vec<int> > amnwatches; 	// 'AMN_watches[lit]' is a list of all AMN clauses indices in which lit occurs

	/**
	 * IMPORTANT, IS CALLED FROM propagate(), NOT EXTERNALLY
	 *
	 * AMN propagation:
	 * 		if p does not occur in any AMN, return
	 * 		if p occurs in an AMN, and its counter is == 0
	 * 			for each other atom q
	 * 				if q == FALSE, nothing
	 * 				if q == TRUE, add learned clause ~p | ~q
	 * 							  CONFLICT, so return ~p | ~q
	 * 				if q == UNKNOWN, add learned clause ~p | ~q
	 * 								 call setTrue(q)
	 */
	Clause* amnpropagate(Lit p);

	/**
	 * Has to reduce the counter of amn statements in which l occurs
	 */
	void 	cardbacktrack 	( Lit l);

	// Debug:
	void     printLit         (Lit l);
	template<class C>
	void     printClause      (const C& c);
};

//=======================
//INLINE METHODS
//=======================

inline void AMNSolver::backtrack ( Lit l){
	if(empty){ return; }
	cardbacktrack(l);
}

//@pre: conflicts are empty
inline bool AMNSolver::simplify(){
	return true;
}

inline Clause* AMNSolver::propagate(Lit p, Clause* confl){
	if(empty || confl != NULL){	return confl; }
	return amnpropagate(p);
}

#endif /* AMNSolver_H_ */
