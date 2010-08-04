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

#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>

#include "solvers/aggsolver/AggTypes.hpp"

namespace Aggrs{
	class Agg;
	class AggrSet;
	class AggrWatch;
	class AggrReason;

	typedef Agg* pAgg;
	typedef vector<pAgg> lsagg;

	typedef AggrSet* pSet;
}

#include "solvers/pcsolver/ISolver.hpp"
typedef PCSolver* pPCSolver;

class AggSolver;
typedef AggSolver* pAggSolver;

using namespace Aggrs;

/*
 * CLAUSE LEARNING INVARIANT:
 * The conflicting clause always contains at least one literal of the current decision level.
 * When doing incomplete propagation, as is currently the case with aggregates, this does not always happen
 * (when he only later derives that a certain literal was already entailed, extra backtracking should occur
 * before doing conflict analysis and backtracking further). The IDsolver already does this, when using the
 * heuristic to delay propagations.
 */

class AggSolver: public tr1::enable_shared_from_this<AggSolver>, public ISolver{
public:
	AggSolver(pPCSolver s);
	virtual ~AggSolver();

	/////////////////////SOLVER NECESSARY
	void 		backtrack 		(const Lit& l);

	/*
	 * Returns the explanation for the deduction of p from an aggregate expression.
	 * This method constructs, from the AggrReason stored for it, a "reason clause" usable in clause learning.
	 * @post the first element in the reason clause will be the literal itself (invariant by minisat!)
	 * @post the clause is added to the sat solver
	 * @returns NON-OWNING pointer
	 */
	rClause 	getExplanation	(const Lit& p);
	void 		notifyVarAdded	(uint64_t nvars); 		//correctly initialize AMNSolver datastructures when vars are added
	rClause 	propagate	(const Lit& p);
	/////////////////////ENDSOLVER NECESSARY

	/////////////////////IDSOLVER NECESSARY
	void 		propagateJustifications(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, vec<int> &nb_body_lits_to_justify);

	bool 		findJustificationAggr(Var head, vec<Lit>& jstf);

	bool 		directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	void 		createLoopFormula(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);

	/**
	 * Adds the heads of the aggregates in which x occurs as a body literal to heads
	 */
	void 		getHeadsOfAggrInWhichOccurs(Var x, vec<Var>& heads);

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
	bool    	addSet       (int id, const vec<Lit>& l, const vector<Weight>& w);

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
	bool    	addAggrExpr  (int defn, int set_id, Weight bound, bool lower, AggrType type, bool defined);

	/**
	 * Checks presence of aggregates and initializes all counters.
	 * UNSAT is set to true if unsat is detected
	 * PRESENT is set to true if aggregate propagations should be done
	 */
	void    	finishECNF_DataStructures (bool& present, bool& unsat); //throws UNSAT

	void 		removeHeadWatch(Var x);
	/////////////////////END INITIALIZATION

	//are used by agg.c, but preferably should be move into protected again
	rClause 	notifySATsolverOfPropagation(const Lit& p, Aggrs::AggrReason* cr);	// Like "enqueue", but for aggregate propagations.

	//Optimisation support
	bool 		addMnmzSum		(Var headv, int setid, bool lower);
    bool 		invalidateSum	(vec<Lit>& invalidation, Var head);
    void 		propagateMnmz	(Var head);

protected:
	/**
	 * Returns the aggregate in which the given variable is the head.
	 */
    pAgg		getAggWithHeadOccurence	(Var v) const;

	vector<pSet>	aggrminsets;
	vector<pSet>	aggrmaxsets;
	vector<pSet>	aggrsumsets;
	vector<pSet>	aggrprodsets;

	vector<AggrReason*>			aggr_reason;	// For each atom, like 'reason'.
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
	void 		doBacktrack(const Lit& l);

	/**
	 * Goes through all watches and propagates the fact that p was set true.
	 */
	rClause 	Aggr_propagate		(const Lit& p);

	bool 		maxAggAsSAT(bool defined, bool lower, Weight bound, const Lit& head, const AggrSet& set);
	bool		finishSets(vector<pSet>& sets); //throws UNSAT
};

//=======================
//INLINE METHODS
//=======================

inline void AggSolver::backtrack (const Lit& l){
	if(!isInitialized()){ return; }
	doBacktrack(l);
}

inline rClause AggSolver::propagate(const Lit& p){
	if (!isInitialized()) {return nullPtrClause;}
	return Aggr_propagate(p);
}

#endif /* AggSolver_H_ */
