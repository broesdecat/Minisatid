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
#include <map>
#include <set>

#include "solvers/pcsolver/SolverModule.hpp"
class PCSolver;
typedef PCSolver* pPCSolver;

class WL;
typedef vector<WL> vwl;

namespace Aggrs{
	typedef vector<Weight> vw;
	typedef vector<Lit> vl;

	class Agg;
	class AggSet;
	typedef Agg* pagg;
	typedef vector<Agg*> vpagg;
	typedef AggSet* pset;

	class AggComb;
	typedef AggComb* pcomb;

	class Watch;
	typedef Watch* pw;

	class AggReason;
}

using namespace Aggrs;

/*
 * CLAUSE LEARNING INVARIANT:
 * The conflicting clause always contains at least one literal of the current decision level.
 * When doing incomplete propagation, as is currently the case with aggregates, this does not always happen
 * (when he only later derives that a certain literal was already entailed, extra backtracking should occur
 * before doing conflict analysis and backtracking further). The IDsolver already does this, when using the
 * heuristic to delay propagations.
 */

class AggSolver: public tr1::enable_shared_from_this<AggSolver>, public SolverModule{
public:
	AggSolver(pPCSolver s);
	virtual ~AggSolver();

	//////
	// INITIALIZATION
	//////

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
	bool addSet(int id, const vector<Lit>& l, const vector<Weight>& w);

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
	bool addAggrExpr(int defn, int set_id, Weight bound, Bound boundsign, AggrType type, HdEq headeq);

	/**
	 * Checks presence of aggregates and initializes all counters.
	 * UNSAT is set to true if unsat is detected
	 * PRESENT is set to true if aggregate propagations should be done
	 */
	void finishECNF_DataStructures 	(bool& present, bool& unsat); //throws UNSAT
	void findClausalPropagations		();
	void removeHeadWatch				(Var x);

	//////
	// SEARCH
	//////
	void backtrack 					(const Lit& l);

	/*
	 * Returns the explanation for the deduction of p from an aggregate expression.
	 * This method constructs, from the AggReason stored for it, a "reason clause" usable in clause learning.
	 * @post the first element in the reason clause will be the literal itself (invariant by minisat!)
	 * @post the clause is added to the sat solver
	 * @returns NON-OWNING pointer
	 */
	rClause getExplanation				(const Lit& p);
	void 	notifyVarAdded				(uint64_t nvars); 		//correctly initialize AMNSolver datastructures when vars are added
	rClause propagate					(const Lit& p);

	//are used by agg.c, but preferably should be move into protected again
	rClause	notifySATsolverOfPropagation(const Lit& p, Aggrs::AggReason* cr);	// Like "enqueue", but for aggregate propagations.

	//////
	// OPTIMISATION
	//////
	bool 	addMnmzSum					(Var headv, int setid, Bound boundsign);
    bool 	invalidateSum				(vec<Lit>& invalidation, Var head);
    void 	propagateMnmz				(Var head);

	//////
	// RECURSIVE AGGREGATES
	//////
	void 	propagateJustifications		(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, vec<int> &nb_body_lits_to_justify);
	void 	findJustificationAggr		(Var head, vec<Lit>& jstf);
	bool 	directlyJustifiable			(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	void 	addExternalLiterals			(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);

	/**
	 * Returns a vector containing the heads of the aggregates in which x occurs as a set literal
	 */
	vector<Var> getHeadsOfAggrInWhichOccurs(Var x);

	/**
	 * Returns the set literals of the aggregate with the given head x.
	 */
	vwl::const_iterator getAggLiteralsBegin	(Var x) const;
	vwl::const_iterator getAggLiteralsEnd	(Var x) const;

	///////
	// Watched literal sets
	///////
	void setHeadWatch(Var head, Agg* agg);
	void addPermWatch(Var v, pw w);
	void addTempWatch(const Lit& l, pw w);

protected:
	/**
	 * Returns the aggregate in which the given variable is the head.
	 */
    pagg 		getAggWithHeadOccurence	(Var v) const;

    map<AggrType, int > 	maptype;
	vector<vector<pcomb> >	sets;			//After initialization, all remaining sets.

	vector<AggReason*>		aggr_reason;	// For each atom, like 'reason'.

	vector<vector<pw> >		tempwatches;
	vector<vector<pw> >		permwatches;	// Aggr_watches[v] is a list of sets in which VAR v occurs (each AggrWatch says: which set, what type of occurrence).

	//index on VAR (heads are always positive
	vector<pagg>			head_watches;	//	does NOT own the pointers
	vector<vector<pcomb> >	network;		// the pointer network of set var -> set

	/**
	 * Correct the min and max values of the aggregates in which l was propagated and delete any aggregate reasons
	 * present.
	 *
	 * @optimization possible: for each decision level, put the current values on a stack. Instead of recalculating it
	 * for each literal, pop the values once for each decision level
	 *
	 * @PRE: backtracking is in anti-chronologous order and all literals are visited!
	 */
	void 		doBacktrack			(const Lit& l);

	/**
	 * Goes through all watches and propagates the fact that p was set true.
	 */
	rClause 	Aggr_propagate	(const Lit& p);

	bool		finishSets		(vector<pcomb>& sets); //throws UNSAT
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
