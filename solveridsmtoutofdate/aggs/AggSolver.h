#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>

#include "Vec.h"
#include "Sort.h"

#include "solverfwd.h"
#include "AggTypes.h"

namespace Aggrs{
	class Agg;
	class AggrSet;
	class AggrWatch;
	class AggrReason;

	typedef Agg* pAgg;
	typedef vector<pAgg> lsagg;

	typedef AggrSet* pSet;
}

#include "IDSolver.h"
#include "Solver.h"

class IDSolver;
class AggSolver;
class Solver;
typedef shared_ptr<IDSolver> pIDSolver;
typedef weak_ptr<IDSolver> wpIDSolver;
typedef shared_ptr<AggSolver> pAggSolver;
typedef weak_ptr<AggSolver> wpAggSolver;
typedef shared_ptr<Solver> pSolver;
typedef weak_ptr<Solver> wpSolver;

using namespace Aggrs;

/*
 * CLAUSE LEARNING INVARIANT:
 * The conflicting clause always contains at least one literal of the current decision level.
 * When doing incomplete propagation, as is currently the case with aggregates, this does not always happen
 * (when he only later derives that a certain literal was already entailed, extra backtracking should occur
 * before doing conflict analysis and backtracking further). The IDsolver already does this, when using the
 * heuristic to delay propagations.
 */

class AggSolver: public enable_shared_from_this<AggSolver>{
private:
	wpSolver	solver;
	wpIDSolver	idsolver;
public:
	AggSolver();
	virtual ~AggSolver();

	/////////////////////SOLVER NECESSARY
	void 	backtrack 		(const Lit& l);

	/*
	 * Returns the explanation for the deduction of p from an aggregate expression.
	 * This method constructs, from the AggrReason stored for it, a "reason clause" usable in clause learning.
	 * @post the first element in the reason clause will be the literal itself (invariant by minisat!)
	 * @post the clause is not saved, so HAS to be deleted after use
	 */
	Clause* getExplanation	(const Lit& p);
	void 	notifyVarAdded	(int nvars); 		//correctly initialize AMNSolver datastructures when vars are added
	Clause* propagate	(const Lit& p);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////IDSOLVER NECESSARY
	void propagateJustifications(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, vec<int> &nb_body_lits_to_justify);

	bool findJustificationAggr(Var head, vec<Lit>& jstf);

	bool directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	void createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);

	/**
	 * Adds the heads of the aggregates in which x occurs as a body literal to heads
	 */
	void getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads);

	/**
	 * Returns the set literals of the aggregate with the given head x.
	 */
	lwlv::const_iterator getAggLiteralsBegin(Var x) const;
	lwlv::const_iterator getAggLiteralsEnd(Var x) const;
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
	void    addSet       (int id, vec<Lit>& l, vector<Weight>& w);

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
	void    addAggrExpr  (int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined);

	/**
	 * Checks presence of aggregates and initializes all counters.
	 * @Return: true if there are aggregates present
	 */
	bool    finishECNF_DataStructures ();

	void 		setSolver				(pSolver s)		{ solver = wpSolver(s); }
	void 		setIDSolver				(pIDSolver s)	{ idsolver = wpIDSolver(s); }
	pSolver		getSolver				()	const		{ return solver.lock(); }
	pIDSolver	getIDSolver				()	const		{ return idsolver.lock(); }
	void		resetIDSolver			()				{ idsolver.reset(); }
	void 		remove					();

	void 		removeHeadWatch(Var x);
	/////////////////////END INITIALIZATION

	//are used by agg.c, but preferably should be move into protected again
	Clause* notifySATsolverOfPropagation(const Lit& p, Aggrs::AggrReason* cr);	// Like "enqueue", but for aggregate propagations.

	// Debug:
	void    printAggrExpr   (pAgg ae);

	//Optimisation support
	void 	addMnmzSum		(Var headv, int setid, bool lower);
    bool 	invalidateSum	(vec<Lit>& invalidation, Var head);
    void 	propagateMnmz	(Var head);

protected:
	/**
	 * Returns the aggregate in which the given variable is the head.
	 */
    pAgg	getAggWithHeadOccurence	(Var v) const;

	vector<pSet>	aggrminsets;
	vector<pSet>	aggrmaxsets;
	vector<pSet>	aggrsumsets;
	vector<pSet>	aggrprodsets;

	vector<AggrReason*>	aggr_reason;	// For each atom, like 'reason'.
	vector<vector<AggrWatch> >	aggr_watches;	// Aggr_watches[v] is a list of sets in which VAR v occurs (each AggrWatch says: which set, what type of occurrence).

	//index on VAR (heads are always positive
	vector<pAgg>				head_watches;	//	does NOT own the pointers
	vector<pAgg> 				aggregates;		//A vector to store all created aggregates as shared pointers, to allow easy destruction in the end
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
	void 	doBacktrack(const Lit& l);

	bool		init;	//indicates whether still in initialization mode

	/**
	 * Goes through all watches and propagates the fact that p was set true.
	 */
	Clause* Aggr_propagate		(const Lit& p);

	void 	maxAggAsSAT(bool defined, bool lower, Weight bound, const Lit& head, const AggrSet& set);
	void	finishSets(vector<pSet>& sets);
};

//=======================
//INLINE METHODS
//=======================

inline void AggSolver::backtrack (const Lit& l){
	if(init){ return; }
	doBacktrack(l);
}

inline Clause* AggSolver::propagate(const Lit& p){
	if (init) {return NULL;}
	return Aggr_propagate(p);
}

#endif /* AggSolver_H_ */
