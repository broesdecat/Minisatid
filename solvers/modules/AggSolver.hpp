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

#include "solvers/utils/Utils.hpp"
#include "solvers/modules/DPLLTmodule.hpp"

namespace MinisatID {

//FIXME correct notion of upper and lower bound!

class PCSolver;
typedef PCSolver* pPCSolver;

class WL;
typedef std::vector<WL> vwl;

namespace Aggrs{
	class Agg;
	class TypedSet;
	class Watch;
	class AggReason;
}

typedef std::vector<Weight> vw;
typedef std::vector<Lit> vl;
typedef std::map<int, Aggrs::TypedSet*> mips;
typedef std::vector<Aggrs::Agg*> vpagg;
typedef std::vector<Aggrs::TypedSet*> vps;
typedef std::vector<vps> vvps;
typedef std::vector<Aggrs::Watch*> vpw;
typedef std::vector<vpw> vvpw;

/*
 * CLAUSE LEARNING INVARIANT:
 * The conflicting clause always contains at least one literal of the current decision level.
 * When doing incomplete propagation, as is currently the case with aggregates, this does not always happen
 * (when he only later derives that a certain literal was already entailed, extra backtracking should occur
 * before doing conflict analysis and backtracking further). The IDsolver already does this, when using the
 * heuristic to delay propagations.
 */

class AggSolver: public DPLLTmodule{
private:
	mips 					_parsedSets;
    vps						_sets;
    std::set<Var>			aggheads;	//A set of all heads that are already used by an aggregate.

	std::vector<Aggrs::AggReason*>	aggreason;	// For each atom, like 'reason'.

	vvpw					tempwatches;	//NON-OWNED PARTIAL WATCHES
	vvpw 					permwatches;	// Aggr_watches[v] is a list of sets in which VAR v occurs (each AggrWatch says: which set, what type of occurrence).
	std::vector<Aggrs::Agg*>	headwatches;	//	index on VARs (heads always positive), does NOT own the pointers
	vvps					network;		// the pointer network of set var -> set

	//statistics
	uint64_t propagations; //Number of propagations into aggregate sets made

	//new trail datastructure
	std::vector<std::vector<Aggrs::TypedSet*> > 	trail;

public:
	AggSolver(pPCSolver s);
	virtual ~AggSolver();

	//Returns the current decision level
	int 				getLevel				() 		const { return trail.size()-1; }

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
	bool 				addSet					(int id, const std::vector<Lit>& l, const std::vector<Weight>& w);

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
	bool 				addAggrExpr				(int defn, int set_id, Weight bound, AggSign boundsign, AggType type, AggSem headeq);

	void 				findClausalPropagations	();

	void 				notifyDefinedHead		(Var head);

	void 				removeHeadWatch			(Var x);

	//////
	// SEARCH
	//////

	virtual void 		notifyVarAdded			(uint64_t nvars);

	/**
	 * Checks presence of aggregates and initializes all counters.
	 * UNSAT is set to true if unsat is detected
	 * PRESENT is set to true if aggregate propagations should be done
	 */
	virtual void 		finishParsing		 	(bool& present, bool& unsat);
	virtual bool 		simplify				() { return true; }; //False if problem unsat
	/**
	 * Goes through all watches and propagates the fact that p was set true.
	 */
	virtual rClause 	propagate				(const Lit& l);
	virtual rClause	 	propagateAtEndOfQueue	();

	virtual void 		newDecisionLevel		();
	virtual void 		backtrackDecisionLevels	(int nblevels, int untillevel);
	virtual rClause 	getExplanation			(const Lit& l);

	virtual const char* getName					() { return "aggregate"; }
	virtual void 		print					();
	virtual void 		printStatistics			() const;

	//are used by agg.c, but preferably should be move into protected again
	rClause				notifySolver(Aggrs::AggReason* cr);	// Like "enqueue", but for aggregate propagations.

	//////
	// OPTIMISATION
	//////
	bool 				addMnmzSum				(Var headv, int setid, AggSign boundsign);
    bool 				invalidateSum			(vec<Lit>& invalidation, Var head);
    void 				propagateMnmz			(Var head);

	//////
	// RECURSIVE AGGREGATES
	//////
	void 				propagateJustifications	(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, vec<int> &nb_body_lits_to_justify);
	void 				findJustificationAggr	(Var head, vec<Lit>& jstf);
	bool 				directlyJustifiable		(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust);
	void 				addExternalLiterals		(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, vec<int>& seen);

	/**
	 * Returns a std::vector containing the heads of the aggregates in which x occurs as a set literal
	 */
	std::vector<Var> 	getAggHeadsWithBodyLit	(Var x);

	/**
	 * Returns the set literals of the aggregate with the given head x.
	 */
	vwl::const_iterator getAggLiteralsBegin		(Var x) const;
	vwl::const_iterator getAggLiteralsEnd		(Var x) const;

	///////
	// Watched literal sets
	///////
	void 				setHeadWatch			(Var head, Aggrs::Agg* agg);
	void 				addPermWatch			(Var v, Aggrs::Watch* w);
	void 				addTempWatch			(const Lit& l, Aggrs::Watch* w);

	void				addToTrail				(Aggrs::TypedSet* set) { trail.back().push_back(set); }

protected:
	mips&				parsedSets				() { return _parsedSets; }
	vps&				sets					() { return _sets; }

	// Returns the aggregate in which the given variable is the head.
	Aggrs::Agg* 		getAggWithHead			(Var v) const;

	bool				finishSet				(Aggrs::TypedSet* set);

	void 				print(Aggrs::Agg* agg) const;
};

}

#endif /* AggSolver_H_ */
