#ifndef AMOSolver_H_
#define AMOSolver_H_

#include <cstdio>

#include "Vec.h"
#include "Alg.h"

#include "SolverTypes.h"
#include "Solver.h"

class Solver;

class AMOSolver{
public:
	AMOSolver();
	virtual ~AMOSolver();

	/////////////////////SOLVER NECESSARY
	bool 	simplify	();
	void 	backtrack 	( Lit l);
	void 	notifyVarAdded	(); 		//correctly initialized AMOSolver datastructures when vars are added
	Clause* 	propagate		(Lit p, Clause* confl);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////INITIALIZATION
	bool    addAMO       (vec<Lit>& ps);                           // Add an At most one statement to the solver.
	void    finishECNF_DataStructures ();                          // Initialize the ECNF data structures. NOTE: aggregates may set the "ok" value to false!

	void setSolver(Solver* s){
		solver = s;
	}

	int       verbosity;          // Verbosity level. 0=silent, 1=some progress report
	/////////////////////END INITIALIZATION

protected:
	lbool	value(Var x) const;
	lbool	value(Lit p) const;
	int		nVars()      const;

	uint64_t amo_statements, amo_literals;
	bool 	init;				//indicates whether still in initialization mode
	bool 	empty; 				//indicates no amo statements are present, so always return from T call

	Solver* solver;

	vec<vec<Clause*> >    AMO_watches;           // 'AMO_watches[lit]' is a list of AMO-constraints watching 'lit' (will go there if literal becomes true). NOTE: the statement is stored as a normal clause!
	Clause*               AMO_propagate(Lit p);  // Perform AMO-propagation. Returns possibly conflicting clause.

	// Debug:
	void     printLit         (Lit l);
	template<class C>
	void     printClause      (const C& c);
};

#endif /* AMOSolver_H_ */
