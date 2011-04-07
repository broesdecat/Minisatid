/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>
#include <map>
#include <set>

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/DPLLTmodule.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class PCSolver;

class WL;
typedef std::vector<WL> vwl;

class Agg;
class TypedSet;
class Watch;
class AggReason;
struct AggBound;

typedef std::map<int, TypedSet*> mips;
typedef std::vector<Agg*> agglist;
typedef std::vector<TypedSet*> setlist;
typedef std::vector<Watch*> watchlist;

typedef std::vector<Weight> vw;
typedef std::vector<Lit> vl;

/*
 * CLAUSE LEARNING INVARIANT:
 * The conflicting clause always contains at least one literal of the current decision level.
 * When doing incomplete propagation, as is currently the case with aggregates, this does not always happen
 * (when he only later derives that a certain literal was already entailed, extra backtracking should occur
 * before doing conflict analysis and backtracking further). The IDsolver already does this, when using the
 * heuristic to delay propagations.
 */

struct LI{
	lbool v;
	int i;
	LI():v(l_Undef), i(0){}
	LI(lbool v, int i): v(v), i(i){}
};

struct VI{
	Var var;
	int heurval;

	bool operator <(const VI& rhs) const{
		return heurval<rhs.heurval;
	}
};

class AggSolver: public DPLLTmodule{
	//TODO pimpl
private:
	mips 					parsedSets;
	std::set<Var>					heads;
	Var								dummyhead;
		// To prevent creating lots of heads which are all certainly true, it is possible to give them all the same (this) head.
		// The aggregates have to be completion defined!

	setlist					sets;
	std::vector<AggReason*>	reasons; 				//Map var to reason

	std::vector<watchlist>	lit2dynamicwatchlist;	// map lit to watches
	std::vector<watchlist>	lit2staticwatchlist;	// map lit to watches
	std::vector<Agg*>		lit2headwatchlist;		// map lit to watches
	std::set<Agg*>			dummyheadtrue2watchlist;	// map dummylittrue to watches
	std::set<Agg*>			dummyheadfalse2watchlist;	// map dummyvarfalse to watches
	std::vector<setlist>	var2setlist;			// the pointer network of set var -> set

	//statistics
	uint64_t 				propagations;

	//new trail datastructure
	std::vector<setlist > 	setsbacktracktrail;
	setlist 				setspropagatetrail;

	std::vector<int>		mapdecleveltotrail;
	int 					index; //fulltrail index?
	uint					propindex;
	std::vector<Lit>		littrail;
	std::vector<LI>			propagated;

	Agg*					optimagg;

	//custom heur
	std::set<Var>			heurvars; //log n instead of direct (but probably important size reduction)
	std::vector<VI>			varwithheurval;

public:
	AggSolver(PCSolver* s);
	virtual ~AggSolver();

	Minisat::Solver*		getSATSolver () const;

	// INITIALIZATION

	/**
	 * Adds the set with the given id to the solver and sets its literals and its weights.
	 *
	 * @pre: no set with the same id has already been added
	 * @pre: negative weights are not allowed
	 * @pre: empty sets are not allowed
	 */
	bool 		addSet(int id, const std::vector<Lit>& l, const std::vector<Weight>& w);

	//@pre: no weights==0 when using a product aggregate
	bool 		addAggrExpr(int defn, int set_id, const Weight& bound, AggSign boundsign, AggType type, AggSem sem, int defid);

	bool 		addMnmz(Var headv, int setid, AggType type);

	// SEARCH
	void 		notifyVarAdded(uint64_t nvars);

	/**
	 * Checks presence of aggregates and initializes all counters.
	 * UNSAT is set to true if unsat is detected
	 * PRESENT is set to true if aggregate propagations should be done
	 */
	void 		finishParsing		 	(bool& present, bool& unsat);

	bool 		simplify				() { return true; }; //False if problem unsat

	/**
	 * Goes through all watches and propagates the fact that p was set true.
	 */
	rClause 	propagate				(const Lit& l);
	rClause	 	propagateAtEndOfQueue	();

	void 		newDecisionLevel		();
	void 		backtrackDecisionLevels	(int nblevels, int untillevel);
	rClause 	getExplanation			(const Lit& l);

	Var			changeBranchChoice 		(const Var& chosenvar);
	void 		adaptAggHeur			(const vwl& wls, int nbagg);

	// INFORMATION

	const char* getName					() const { return "aggregate"; }
	void 		printState				() const;
	void 		printStatistics			() const;

	// VERIFICATION

	bool 		checkStatus				();

	// OPTIMISATION
    bool 		invalidateAgg			(vec<Lit>& invalidation);
    void 		propagateMnmz			();

	// RECURSIVE AGGREGATES
	void 		propagateJustifications		(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, VarToJustif &nb_body_lits_to_justify);
	void 		findJustificationAggr		(Var head, vec<Lit>& jstf);
	bool 		directlyJustifiable			(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust);
	void 		addExternalLiterals			(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, VarToJustif& seen);
	std::vector<Var> 	getDefAggHeadsWithBodyLit		(Var x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadBegin(Var x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadEnd	(Var x) const;

	//INTERNAL (TODO into pimpl)
	rClause		notifySolver(AggReason* cr);
	rClause 	doProp					();
	void 		findClausalPropagations();
	void 		notifyDefinedHead		(Var head, int defID);
	void 		removeHeadWatch			(Var head, int defID);
	void 		setHeadWatch			(Lit head, Agg* agg);
	void 		addStaticWatch			(Var v, Watch* w);
	void 		addDynamicWatch			(const Lit& l, Watch* w);
	const std::vector<TypedSet*>&	getPropTrail	() const { return setspropagatetrail; }
	void		addToPropTrail			(TypedSet* set) { setspropagatetrail.push_back(set); }
	void		addToBackTrail			(TypedSet* set) { setsbacktracktrail.back().push_back(set); }
	void		addRootLevel			();
	int			getTime					(Lit l) const;

	void		setOptimAgg				(Agg* agg) { optimagg = agg; }
	bool		isOptimAgg				(Agg const * const agg) { return optimagg==agg; }

protected:
	Agg*		getOptimAgg				() 				{ return optimagg; }

	void 		adaptToNVars			(uint64_t nvars);
	int 		getCurrentDecisionLevel	() 		const { return setsbacktracktrail.size()-1; }

	Agg*		getAggDefiningHead		(Var v) const;

	bool		finishSet				(TypedSet* set);

	bool 		addAggrExpr				(Var headv, int setid, const AggBound& bound, AggType type, AggSem sem, int defid);

};

void printNumberOfAggregates(int nbsets, int nbagg, int nbsetlits, std::map<MinisatID::AggType, int>& nbaggs, int verbosity = 1000);

}

#endif /* AggSolver_H_ */
