//LICENSEPLACEHOLDER
#ifndef AggSolver_H_
#define AggSolver_H_

#include <cstdio>
#include <map>
#include <set>

#include "modules/aggsolver/AggUtils.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

///////
// Aggregate information
///////

class PCSolver;

class WL;
typedef std::vector<WL> vwl;

namespace Aggrs{
	class Agg;
	class TypedSet;
	class Watch;
	class AggReason;
	struct AggBound;

	typedef std::map<int, Aggrs::TypedSet*> mips;
	typedef std::vector<Aggrs::Agg*> agglist;
	typedef std::vector<Aggrs::TypedSet*> setlist;
	typedef std::vector<Aggrs::Watch*> watchlist;
}

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

class AggSolver: public DPLLTmodule{
	//TODO pimpl
private:
	Aggrs::mips 	parsedSets;
	std::set<Var>	heads;

	Aggrs::setlist	sets;//LICENSEPLACEHOLDER
	std::vector<Aggrs::AggReason*>	reasons; //Map var to reason

	std::vector<Aggrs::watchlist>	lit2dynamicwatchlist;	// map lit to watches
	std::vector<Aggrs::watchlist>	lit2staticwatchlist;	// map lit to watches
	std::vector<Aggrs::Agg*>		lit2headwatchlist;	// map lit to watches
	std::vector<Aggrs::setlist>		var2setlist;		// the pointer network of set var -> set

	//statistics
	uint64_t propagations;

	//new trail datastructure
	std::vector<Aggrs::setlist > 	setsbacktracktrail;
	Aggrs::setlist 					setspropagatetrail;

	std::vector<int>								mapdecleveltotrail;
	int 											index; //fulltrail index?
	uint											propindex;
	std::vector<Lit>								littrail;
	std::vector<LI>									propagated;

public:
	AggSolver(PCSolver* s);
	virtual ~AggSolver();

	// INITIALIZATION

	/**
	 * Adds the set with the given id to the solver and sets its literals and its weights.
	 *
	 * @pre: no set with the same id has already been added
	 * @pre: negative weights are not allowed
	 * @pre: empty sets are not allowed
	 */
	bool addSet(int id, const std::vector<Lit>& l, const std::vector<Weight>& w);

	/**
	 * @pre: no weights==0 when using a product aggregate
	 */
	bool addAggrExpr(int defn, int set_id, const Weight& bound, AggSign boundsign, AggType type, AggSem headeq);

	bool addMnmz(Var headv, int setid, AggType type);

	// SEARCH
	void notifyVarAdded(uint64_t nvars);

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

	// INFORMATION

	const char* getName					() const { return "aggregate"; }
	void 		print					() const;
	void 		printStatistics			() const;

	// VERIFICATION

	bool 		checkStatus				();

	// OPTIMISATION
    bool 				invalidateAgg			(vec<Lit>& invalidation, Var head);
    void 				propagateMnmz			(Var head);

	// RECURSIVE AGGREGATES
	void 				propagateJustifications		(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& v, VarToJustif &nb_body_lits_to_justify);
	void 				findJustificationAggr		(Var head, vec<Lit>& jstf);
	bool 				directlyJustifiable			(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust);
	void 				addExternalLiterals			(Var v, const std::set<Var>& ufs, vec<Lit>& loopf, VarToJustif& seen);
	std::vector<Var> 	getAggHeadsWithBodyLit		(Var x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadBegin(Var x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadEnd	(Var x) const;

	//INTERNAL (TODO into pimpl)
	rClause		notifySolver(Aggrs::AggReason* cr);
	rClause 	doProp					();
	void 		findClausalPropagations();
	void 		notifyDefinedHead(Var head);
	void 		removeHeadWatch(Var x);
	void 		setHeadWatch			(Lit head, Aggrs::Agg* agg);
	void 		addStaticWatch			(Var v, Aggrs::Watch* w);
	void 		addDynamicWatch			(const Lit& l, Aggrs::Watch* w);
	const std::vector<Aggrs::TypedSet*>&	getPropTrail	() const { return setspropagatetrail; }
	void		addToPropTrail			(Aggrs::TypedSet* set) { setspropagatetrail.push_back(set); }
	void		addToBackTrail			(Aggrs::TypedSet* set) { setsbacktracktrail.back().push_back(set); }
	void		addRootLevel			();
	int			getTime					(Lit l) const;

protected:
	int 				getCurrentDecisionLevel	() 		const { return setsbacktracktrail.size()-1; }

	Aggrs::Agg* 		getAggDefiningHead		(Var v) const;

	bool				finishSet				(Aggrs::TypedSet* set);

	bool 				addAggrExpr				(Var headv, int setid, const Aggrs::AggBound& bound, AggType type, AggSem headeq);

};

namespace Aggrs{
	void printNumberOfAggregates(int nbsets, int nbagg, int nbsetlits, std::map<MinisatID::AggType, int>& nbaggs, int verbosity = 1000);
}

}

#endif /* AggSolver_H_ */
