/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef IDSOLVER_H_
#define IDSOLVER_H_

#include <set>
#include <stack>
#include <queue>
#include <vector>
#include <map>

#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

typedef std::vector<int> VarToJustif; //Maps variables to their current state in the justification algorithm

class PCSolver;

/**
 * The different possible types of definitions.
 * If a variable is NONDEFALL, no definition is associated with it.
 * If a variable is NONDEFPOS, a definition is associated with it, but there is no recursion through it in the POSITIVE dependency graph
 * 		but there might be recursion over negation (relevant for the well-founded model)
 */
enum DefType	{ DISJ, CONJ, AGGR };
enum DefOcc 	{ NONDEFOCC, POSLOOP, MIXEDLOOP, BOTHLOOP };
enum UFS 		{ NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK };

class PropRule {
private:
	const Var head;
	litlist lits;

public:
    PropRule(Lit head, const litlist& ps): head(var(head)), lits(ps){}

    int 	size() 				const	{ return lits.size(); }
    Lit 	getHead() 			const	{ return mkLit(head, false); }
    Lit 	operator [](int i) 	const	{ return lits[i]; }
    litlist::const_iterator begin()	const 	{ return lits.begin(); }
    litlist::const_iterator end()	const 	{ return lits.end(); }
};

class IDAgg{
private:
	AggBound	bound;
	Lit			head;
	AggSem		sem;
	int			index;
	AggType		type;
	std::vector<WL> wls;

public:
	IDAgg(const Lit& head, AggBound b, AggSem sem, AggType type, const std::vector<WL>& wls):
		bound(b), head(head), sem(sem), index(-1), type(type), wls(wls){	}

	const Lit& 	getHead		() 					const 	{ return head; }
	void	 	setHead		(const Lit& l)			 	{ head = l; }
	int			getIndex	()					const	{ return index; }

	const Weight&	getBound()					const	{ return bound.bound; }
	bool		hasUB		()					const	{ return bound.sign!=AGGSIGN_LB; }
	bool		hasLB		()					const	{ return bound.sign!=AGGSIGN_UB; }
	AggSign		getSign		()					const	{ return bound.sign; }
	const std::vector<WL>& getWL()				const 	{ return wls; }
	AggType		getType		()					const 	{ return type; }
};

class DefinedVar{
private:
	litlist _reason;
	union{
		PropRule*	_definition;
		IDAgg*		_definedaggregate; // INVARIANT: no initially justified aggregates
	};

	DefType 		_type;
	DefOcc 			_occ;
	bool 			_isCS;			//Currently considered cycle source
	int 			_scc;			//To which SCC it belongs
	litlist 		_justification;	//Its current justification

public:
	DefinedVar(PropRule* rule, DefType type): _definition(rule), _type(type), _occ(BOTHLOOP), _isCS(false), _scc(-1){}
	DefinedVar(IDAgg* rule): _definedaggregate(rule), _type(AGGR), _occ(BOTHLOOP), _isCS(false), _scc(-1){}
	~DefinedVar(){
		if(_type==AGGR){
			delete(_definedaggregate);
		}else{
			delete(_definition);
		}
	}

	litlist& 		reason(){ return _reason; }
	PropRule* 				definition(){ return _definition; }
	IDAgg* 					definedaggregate(){ return _definedaggregate; }
	DefType& 				type(){ return _type; }
	DefOcc& 				occ(){ return _occ; }
	bool &					isCS(){ return _isCS; }
	int &					scc(){ return _scc; }
	litlist& 				justification(){ return _justification; }

	const litlist& reason()const { return _reason; }
	const DefType& 			type()const { return _type; }
	const DefOcc& 			occ()const { return _occ; }
	bool					isCS()const { return _isCS; }
	int						scc()const { return _scc; }
	const litlist& 		justification()const { return _justification; }
};

class IDSolver: public Propagator{
private:
	int definitionID;

	Var minvar, nbvars; //TODO, maxvar, nbvars; 	//The lowest and highest headvariable. INVAR: Definitions will be offset by minvar and the size will be nbvars
	std::vector<DefinedVar*> definitions; //Maps all variables to NULL or a defined variable

	std::vector<varlist > 	_disj_occurs, _conj_occurs, _aggr_occurs;

	InterMediateDataStruct*	_seen;

	DEFSEM					sem;

	bool					posrecagg, mixedrecagg;

	bool 					posloops, negloops;
	varlist		defdVars;	// All the vars that are the head of some kind of definition (disj, conj or aggr). Allows to iterate over all definitions.

	bool					backtracked;	//True if the solver has backtracked between now and the previous search for cycle sources. Is true at the start

	int						adaption_total;     // Used only if defn_strategy==adaptive. Number of decision levels between indirectPropagate() uses.
	int						adaption_current;   // Used only if defn_strategy==adaptive. Number of decision levels left until next indirectPropagate() use.

	// Cycle sources:
	varlist		css;                    // List of cycle sources. May still include atoms v that have !isCS[v].
	std::set<Var>			savedufs;
	InnerDisjunction		savedloopf;


	//Well-founded model checking
	bool 					wffixpoint;
	varlist 		wfroot, wfrootnodes;
	std::queue<Lit> 		wfqueue;
	std::set<Var> 			wfmarkedAtoms;
	std::vector<bool> 		wfisMarked;

	//Statistics
	uint64_t 				atoms_in_pos_loops;
    uint64_t 				cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts;
    uint64_t 				nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;

public:
	IDSolver(PCSolver* s, int definitionID);
	virtual ~IDSolver();

	int					getDefinitionID() const { return definitionID; }

	bool				hasRecursiveAggregates	() const 	{ return posrecagg || mixedrecagg; }

	// Propagator methods
	virtual const char* getName					() const { return "definitional"; }
	virtual int			getNbOfFormulas			() const;
	virtual rClause 	getExplanation			(const Lit& l);
	// Event propagator methods
	virtual void 		finishParsing		 	(bool& present, bool& unsat);
	virtual rClause 	notifypropagate			();
	virtual void 		notifyNewDecisionLevel	();
	virtual void 		notifyBacktrack			(int untillevel, const Lit& decision){ backtracked = true; Propagator::notifyBacktrack(untillevel, decision); };
	virtual void 		printState				() const;
	virtual void 		printStatistics			() const;
	virtual rClause		notifyFullAssignmentFound();


	rClause				isWellFoundedModel		();

	DEFSEM				getSemantics			() const { return sem; }

	const litlist&		getCFJustificationAggr	(Var v) const;
	void 				cycleSourceAggr			(Var v, litlist& nj);

	void 				addDefinedAggregate		(const InnerReifAggregate& agg, const InnerWLSet& set);
	bool    			addRule      			(bool conj, Var head, const litlist& ps);	// Add a rule to the solver.

	bool				isDefined				(Var var) 	const { return hasDefVar(var); }
	bool 				isConjunctive			(Var v)		const {	return type(v) == CONJ; }
	bool 				isDisjunctive			(Var v) 	const {	return type(v) == DISJ;	}
	bool 				isDefinedByAggr			(Var v) 	const {	return type(v) == AGGR;	}
	const PropRule&		getDefinition			(Var var) 	const { assert(hasDefVar(var)); return *definition(var); }

private:
	bool 				simplifyGraph		(); //False if problem unsat

	void 				adaptStructsToHead	(Var head);
	DefinedVar* 		getDefVar			(Var v) const { assert(v>=0 && minvar<=v && v-minvar<nbvars); return definitions[v-minvar]; }
	void				setDefVar			(Var v, DefinedVar* newvar) { assert(v>=0 && minvar<=v && v-minvar<nbvars); definitions[v-minvar] = newvar; }
	bool 				hasDefVar			(Var v) const { return minvar<=v && v-minvar<nbvars && getDefVar(v)!=NULL; }

	bool 				isDefInPosGraph		(Var v) const {	return hasDefVar(v) && (occ(v)==POSLOOP || occ(v)==BOTHLOOP); }

	bool 				canBecomeTrue		(Lit l) const { return value(l) != l_False; }
	bool 				inSameSCC			(Var x, Var y) const { return isDefined(x) && isDefined(y) && scc(x) == scc(y); }

	litlist& 	reason		(Var v){ assert(hasDefVar(v)); return getDefVar(v)->reason(); }
	PropRule const*		definition	(Var v) const { assert(hasDefVar(v)); return getDefVar(v)->definition(); }
	IDAgg *				aggdefinition(Var v) const { assert(hasDefVar(v)); return getDefVar(v)->definedaggregate(); }
	DefType& 			type		(Var v){ assert(hasDefVar(v)); return getDefVar(v)->type(); }
	DefOcc& 			occ			(Var v){ assert(hasDefVar(v)); return getDefVar(v)->occ(); }
	bool &				isCS		(Var v){ assert(hasDefVar(v)); return getDefVar(v)->isCS(); }
	int &				scc			(Var v){ assert(hasDefVar(v)); return getDefVar(v)->scc(); }
	litlist& 			justification(Var v){ assert(hasDefVar(v)); return getDefVar(v)->justification(); }

	const litlist& 	reason		(Var v)const { return getDefVar(v)->reason(); }
	const DefType& 		type		(Var v)const { return getDefVar(v)->type(); }
	const DefOcc& 		occ			(Var v)const { return getDefVar(v)->occ(); }
	bool 				isCS		(Var v)const { return getDefVar(v)->isCS(); }
	int 				scc			(Var v)const { return getDefVar(v)->scc(); }
	const litlist& 	justification(Var v)const { return getDefVar(v)->justification(); }

	bool				hasSeen		(Var v) const 	{ return _seen->hasElem(v); }
	int&				seen		(Var v) 		{ assert(hasSeen(v)); return _seen->getElem(v); }
	const int&			seen		(Var v) const 	{ assert(hasSeen(v)); return _seen->getElem(v); }

	const varlist&	disj_occurs	(const Lit& l) const { return _disj_occurs[toInt(l)]; }
	varlist&		disj_occurs	(const Lit& l) { return _disj_occurs[toInt(l)]; }
	bool	hasdisj_occurs(const Lit& l) const { return disj_occurs(l).size()>0; }
	void	addDisjOccurs(const Lit& l, Var v) { disj_occurs(l).push_back(v); assert(type(v)==DISJ); }

	varlist&		conj_occurs	(const Lit& l) { return _conj_occurs[toInt(l)]; }
	const varlist&	conj_occurs	(const Lit& l) const { return _conj_occurs[toInt(l)]; }
	bool	hasconj_occurs(const Lit& l) const { return conj_occurs(l).size()>0; }
	void	addConjOccurs(const Lit& l, Var v) { conj_occurs(l).push_back(v); assert(type(v)==CONJ); }

	varlist&		aggr_occurs	(const Lit& l) { return _aggr_occurs[toInt(l)]; }
	const varlist&	aggr_occurs	(const Lit& l) const { return _aggr_occurs[toInt(l)]; }
	bool	hasaggr_occurs(const Lit& l) const { return aggr_occurs(l).size()>0; }
	void	addAggrOccurs(const Lit& l, Var v) { aggr_occurs(l).push_back(v); assert(type(v)==AGGR); }

	void	createDefinition(Var head, PropRule* r, DefType type) 	{ defdVars.push_back(head); setDefVar(head, new DefinedVar(r, type));}
	void	createDefinition(Var head, IDAgg* agg) 					{ defdVars.push_back(head); setDefVar(head, new DefinedVar(agg));}
	void	removeDefinition(Var head) { delete getDefVar(head); setDefVar(head, NULL); }

	bool	setTypeIfNoPosLoops	(Var v) const;

	void 	propagateJustificationDisj(const Lit& l, std::vector<litlist>& jstf, litlist& heads);
	void 	propagateJustificationAggr(const Lit& l, std::vector<litlist>& jstf, litlist& heads);
	void 	propagateJustificationConj(const Lit& l, std::queue<Lit>& heads);
	void 	propagateJustificationConj(const Lit& l, litlist& heads);

	void 	findJustificationDisj(Var v, litlist& jstf);
	bool 	findJustificationDisj(Var v, litlist& jstf, varlist& nonjstf);
	bool 	findJustificationConj(Var v, litlist& jstf, varlist& nonjstf);
	bool 	findJustificationAggr(Var v, litlist& jstf, varlist& nonjstf);

	// Justification methods:
	void	apply_changes      ();
	void 	changejust(Var v, litlist& j);

	// Cycle source methods:
	void	addCycleSource				(Var v);
	void	clearCycleSources			();
	void	findCycleSources			();
	void	findJustification			(Var v);
	void 	checkJustification			(Var head);

	// Propagation method:
	rClause  indirectPropagate  		();                        /* Main method.
                                                                      1) Finds cycle sources and supporting justification.
                                                                      2) Applies 'unfounded(..)' on each of them,
                                                                      3) ... asserting an unfounded set as soon as one is found, or
                                                                         applying the changes to 'J' after no unfounded set is found for any cycle source.
	 */

	// Auxiliary for indirectPropagate:
	bool	indirectPropagateNow();                               // Decide (depending on chosen strategy) whether or not to do propagations now.
	bool	unfounded          (Var cs, std::set<Var>& ufs);      // True iff 'cs' is currently in an unfounded set, 'ufs'.
	rClause	assertUnfoundedSet (const std::set<Var>& ufs);

	UFS 	visitForUFSsimple(Var v, std::set<Var>& ufs, int& visittime, varlist& stack, VarToJustif& visited, std::vector<litlist >& network);
	void 	changeJustificationsTarjan(Var definednode, Lit firstjustification, std::vector<litlist >& network, VarToJustif& visited); //changes the justifications of the tarjan algorithm

	bool	visitedEarlierTarjan	(Var x, Var y, const VarToJustif& visitedandjust)	const;
	bool	visitedTarjan			(Var x, const VarToJustif& visitedandjust) 		const;
	int		visitedAtTarjan			(Var x, const VarToJustif& visitedandjust) 		const;
	bool	hasJustificationTarjan	(Var x, const VarToJustif& visitedandjust)			const;

	void	markNonJustified   			(Var cs, varlist& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Var v, Var cs, std::queue<Var> &q, varlist& tmpseen);
	void	markNonJustifiedAddParents	(Var x, Var cs, std::queue<Var> &q, varlist& tmpseen);
	bool	directlyJustifiable			(Var v, std::set<Var>& ufs, std::queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified					(const InterMediateDataStruct& currentjust, Lit x) const;
	bool	isJustified					(const InterMediateDataStruct& currentjust, Var x) const;
	bool 	oppositeIsJustified			(const InterMediateDataStruct& currentjust, const WL& wl, bool real) const;
	bool 	isJustified					(const InterMediateDataStruct& currentjust, const WL& wl, bool real) const;

	bool	propagateJustified			(Var v, Var cs, std::set<Var>& ufs);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified
	void	addLoopfClause				(Lit l, InnerDisjunction& lits);

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, std::vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, varlist& roots); // Method to initialize 'scc'.
	void visitFull(Var i, std::vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, bool throughPositiveLit, varlist& posroots, varlist& rootofmixed, varlist& nodeinmixed);

	// Debug:
	void	print		(const rClause c)	const;
	void	print		(const PropRule& c)	const;
	bool	isCycleFree	() 					const;			// Verifies whether justification is indeed cycle free, not used, for debugging purposes.

	void	addExternalDisjuncts(const std::set<Var>& ufs, litlist& loopf);

	// WELL FOUNDED MODEL CHECKING

	/*
	 * Implementation of Tarjan's algorithm for detecting strongly connected components.
	 */
	void visitWF(Var i, varlist &root, std::vector<bool> &incomp, std::stack<Var> &stack, varlist &visited, int& counter, bool throughPositiveLit, std::vector<int>& rootofmixed);
	/*
	 * Search for mixed cycles in the justification graph of the current model.
	 * @post For every mixed cycle in the justification graph, there is one literal of the cycle on \c _mixedCycleRoots.
	 */
	void findMixedCycles(varlist &root, std::vector<int>& rootofmixed);
	/*
	 * Mark all atoms that are above the mixed cycle roots in the justification graph.
	 */
	void markUpward();
	void mark(Var);
	/*
	 * For marked literal l, set _counters[l] to the number of marked bodyliterals in its body. When l is conj/disj, and contains an false/true unmarked bodyliteral, l is pushed on _queuePropagate.
	 */
	void initializeCounters();
	void forwardPropagate(bool);
	void overestimateCounters();
	void removeMarks();


	bool canJustifyHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const;
	bool canJustifyMaxHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const;
	bool canJustifySPHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const;
	IDAgg* getAggDefiningHead(Var v) const;
	varlist getDefAggHeadsWithBodyLit(Var x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadBegin(Var x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadEnd(Var x) const ;
	void addExternalLiterals(Var v, const std::set<Var>& ufs, litlist& loopf, InterMediateDataStruct& seen);
	void findJustificationAggr(Var head, litlist& outjstf) ;
	bool directlyJustifiable(Var v, litlist& jstf, varlist& nonjstf, InterMediateDataStruct& currentjust);
	bool isInitiallyJustified(const IDAgg& agg);
};

}

#endif /* IDSOLVER_H_ */
