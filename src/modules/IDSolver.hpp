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

#include <cstdio>
#include <set>
#include <stack>
#include <queue>
#include <vector>
#include <map>
#include <tr1/unordered_map>

#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

typedef std::vector<Lit> vl;
typedef std::vector<Var> vv;
typedef std::vector<int> VarToJustif; //Maps variables to their current state in the justification algorithm

class PCSolver;
class AggSolver;

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
	vl lits;

public:
    PropRule(Lit head, const vec<Lit>& ps): head(var(head)){
    	lits.reserve(ps.size());
    	for(int i=0; i<ps.size(); ++i){
    		lits.push_back(ps[i]);
    	}
    }

    int 	size() 				const	{ return lits.size(); }
    Lit 	getHead() 			const	{ return mkLit(head, false); }
    Lit 	operator [](int i) 	const	{ return lits[i]; }
    vl::const_iterator begin()	const 	{ return lits.begin(); }
    vl::const_iterator end()	const 	{ return lits.end(); }
};

class DefinedVar{
private:
	std::vector<Lit> 	_reason;
	PropRule* 			_definition;	//Can be NULL if aggregate
	DefType 			_type;
	DefOcc 				_occ;
	bool 				_isCS;			//Currently considered cycle source
	int 				_scc;			//To which SCC it belongs
	vec<Lit> 			_justification;	//Its current justification

public:
	DefinedVar(PropRule* rule, DefType type): _definition(rule), _type(type), _occ(BOTHLOOP), _isCS(false), _scc(-1){}
	~DefinedVar(){
		delete _definition;
	}

	std::vector<Lit>& 		reason(){ return _reason; }
	PropRule* 				definition(){ return _definition; }
	DefType& 				type(){ return _type; }
	DefOcc& 				occ(){ return _occ; }
	bool &					isCS(){ return _isCS; }
	int &					scc(){ return _scc; }
	vec<Lit>& 				justification(){ return _justification; }

	const std::vector<Lit>& reason()const { return _reason; }
	const DefType& 			type()const { return _type; }
	const DefOcc& 			occ()const { return _occ; }
	bool					isCS()const { return _isCS; }
	int						scc()const { return _scc; }
	const vec<Lit>& 		justification()const { return _justification; }
};

class IDSolver: public DPLLTmodule{
private:
	std::vector<DefinedVar*> definitions; //Maps all variables to NULL or a defined variable

	std::vector<std::vector<Var> > 	_disj_occurs, _conj_occurs;
	//std::map<Var, std::vector<Var> > 	_disj_occurs, _conj_occurs;
	//std::tr1::unordered_map<Var, std::vector<Var> > 	_disj_occurs, _conj_occurs;

	VarToJustif				seen;

	DEFSEM					sem;

	int 					recagg; 	//The number of recursive aggregates present, if 0 after initialization, no aggsolver linking will be used.

	int						previoustrailatsimp; //The size of the trail the previous time simplification was run.

	bool 					posloops, negloops;
	std::vector<Var>		defdVars;	// All the vars that are the head of some kind of definition (disj, conj or aggr). Allows to iterate over all definitions.

	bool					simplified;
	bool					backtracked;	//True if the solver has backtracked between now and the previous search for cycle sources. Is true at the start

	std::set<Var>			toremoveaggrheads; //The set of defined aggregates that are no longer defined and should be removed from IDSolver during simplification.

	int						adaption_total;     // Used only if defn_strategy==adaptive. Number of decision levels between indirectPropagate() uses.
	int						adaption_current;   // Used only if defn_strategy==adaptive. Number of decision levels left until next indirectPropagate() use.

	// Cycle sources:
	std::vector<Var>		css;                    // List of cycle sources. May still include atoms v that have !isCS[v].


	//Well-founded model checking
	bool 					wffixpoint;
	std::vector<Var> 		wfroot, wfrootnodes;
	std::queue<Lit> 		wfqueue;
	std::set<Var> 			wfmarkedAtoms;
	std::vector<bool> 		wfisMarked;

	//Statistics
	uint64_t 				atoms_in_pos_loops;
    uint64_t 				cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts;
    uint64_t 				nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;

public:
	IDSolver(MinisatID::PCSolver* s);
	virtual ~IDSolver();

	MinisatID::AggSolver*	getAggSolver			()	const	{ return recagg==0?NULL:getPCSolver().getAggSolver();}

	virtual void 		notifyVarAdded			(uint64_t nvars);
	virtual void 		finishParsing		 	(bool& present, bool& unsat);
	virtual bool 		simplify				(); //False if problem unsat
	virtual rClause 	propagate				(const Lit& l){ return nullPtrClause; };
	virtual rClause 	propagateAtEndOfQueue	();
	//virtual void 		backtrack				(const Lit& l);
	virtual void 		newDecisionLevel		();
	virtual void 		backtrackDecisionLevels	(int nblevels, int untillevel){ backtracked = true; };
	virtual rClause 	getExplanation			(const Lit& l);

	virtual void 		printStatistics			() const;

	virtual const char* getName					() const { return "definitional"; }
	virtual void 		print					() const;

	bool 				checkStatus				();
	bool 				isWellFoundedModel		();

	DEFSEM				getSemantics			() const { return sem; }

	const vec<Lit>&		getCFJustificationAggr	(Var v) const;
	void 				cycleSourceAggr			(Var v, vec<Lit>& nj);
	void 				notifyAggrHead			(Var head);
	void 				removeAggrHead			(Var head);

	bool    			addRule      			(bool conj, Lit head, const vec<Lit>& ps);	// Add a rule to the solver.

	bool				isDefined				(Var var) 	const { return hasDefVar(var); }
	bool 				isConjunctive			(Var v)		const {	return type(v) == CONJ; }
	bool 				isDisjunctive			(Var v) 	const {	return type(v) == DISJ;	}
	bool 				isDefinedByAggr			(Var v) 	const {	return type(v) == AGGR;	}
	const PropRule&		getDefinition			(Var var) 	const { assert(hasDefVar(var)); return *definition(var); }

private:
	void 				adaptToNVars		(uint64_t nvars);
	bool 				simplifyGraph		(); //False if problem unsat

	DefinedVar* 		getDefVar			(Var v) const { assert(v>=0 && definitions.size()>(uint)v); return definitions[(uint)v]; }
	bool 				hasDefVar			(Var v) const { return getDefVar(v)!=NULL; }

	bool 				isDefInPosGraph		(Var v) const {	return hasDefVar(v) && (occ(v)==POSLOOP || occ(v)==BOTHLOOP); }

	bool 				canBecomeTrue		(Lit l) const { return value(l) != l_False; }
	bool 				inSameSCC			(Var x, Var y) const { return isDefined(x) && isDefined(y) && scc(x) == scc(y); }

	std::vector<Lit>& 	reason		(Var v){ assert(hasDefVar(v)); return getDefVar(v)->reason(); }
	PropRule const*		definition	(Var v) const { assert(hasDefVar(v)); return getDefVar(v)->definition(); }
	DefType& 			type		(Var v){ assert(hasDefVar(v)); return getDefVar(v)->type(); }
	DefOcc& 			occ			(Var v){ assert(hasDefVar(v)); return getDefVar(v)->occ(); }
	bool &				isCS		(Var v){ assert(hasDefVar(v)); return getDefVar(v)->isCS(); }
	int &				scc			(Var v){ assert(hasDefVar(v)); return getDefVar(v)->scc(); }
	vec<Lit>& 			justification(Var v){ assert(hasDefVar(v)); return getDefVar(v)->justification(); }

	const std::vector<Lit>& 	reason		(Var v)const { return getDefVar(v)->reason(); }
	const DefType& 		type		(Var v)const { return getDefVar(v)->type(); }
	const DefOcc& 		occ			(Var v)const { return getDefVar(v)->occ(); }
	bool 				isCS		(Var v)const { return getDefVar(v)->isCS(); }
	int 				scc			(Var v)const { return getDefVar(v)->scc(); }
	const vec<Lit>& 	justification(Var v)const { return getDefVar(v)->justification(); }

	const std::vector<Var>&	disj_occurs	(Lit l) const { return _disj_occurs[toInt(l)]; }
	const std::vector<Var>&	conj_occurs	(Lit l) const { return _conj_occurs[toInt(l)]; }
	bool	hasdisj_occurs(Lit l) const { return _disj_occurs[toInt(l)].size()>0; }
	bool	hasconj_occurs(Lit l) const { return _conj_occurs[toInt(l)].size()>0; }
	void	addDisjOccurs(Lit l, Var v) { assert(((long)_disj_occurs.size())>toInt(l)); _disj_occurs[toInt(l)].push_back(v); assert(type(v)==DISJ); }
	void	addConjOccurs(Lit l, Var v) { assert(((long)_conj_occurs.size())>toInt(l)); _conj_occurs[toInt(l)].push_back(v); assert(type(v)==CONJ); }

	void	createDefinition(Var head, PropRule* r, DefType type) { defdVars.push_back(head);
																		definitions[head] = new DefinedVar(r, type);}
	void	removeDefinition(Var head) { delete definitions[head]; definitions[head]=NULL; }

	bool	setTypeIfNoPosLoops	(Var v) const;

	void 	propagateJustificationDisj(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads);
	void 	propagateJustificationAggr(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads);
	void 	propagateJustificationConj(Lit l, vec<Lit>& heads);

	void 	findJustificationDisj(Var v, vec<Lit>& jstf);
	bool 	findJustificationDisj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust);
	bool 	findJustificationConj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust);
	bool 	findJustificationAggr(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, VarToJustif& currentjust);

	// Justification methods:
	void	apply_changes      ();
	void 	changejust(Var v, vec<Lit>& j);

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

	UFS 	visitForUFSsimple	(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, VarToJustif& visited, vec<vec<Lit> >& network);
	void 	changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, VarToJustif& visited); //changes the justifications of the tarjan algorithm

	bool	visitedEarlierTarjan	(Var x, Var y, const VarToJustif& visitedandjust)	const;
	bool	visitedTarjan			(Var x, const VarToJustif& visitedandjust) 		const;
	int		visitedAtTarjan			(Var x, const VarToJustif& visitedandjust) 		const;
	bool	hasJustificationTarjan	(Var x, const VarToJustif& visitedandjust)			const;

	void	markNonJustified   			(Var cs, vec<Var>& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Var v, Var cs, std::queue<Var> &q, vec<Var>& tmpseen);
	void	markNonJustifiedAddParents	(Var x, Var cs, std::queue<Var> &q, vec<Var>& tmpseen);
	bool	directlyJustifiable			(Var v, std::set<Var>& ufs, std::queue<Var>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified					(Lit x) const;
	bool	isJustified					(Var x) const;
	bool	propagateJustified			(Var v, Var cs, std::set<Var>& ufs);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified
	void	addLoopfClause				(Lit l, vec<Lit>& lits);

	// Another propagation method (too expensive in practice):
	// void     fwIndirectPropagate();

	void visit(Var i, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter); // Method to initialize 'scc'.
	void visitFull(Var i, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter, bool throughPositiveLit, vec<int>& rootofmixed, vec<Var>& nodeinmixed);

	// Debug:
	void	print		(const rClause c)	const;
	void	print		(const PropRule& c)	const;
	bool	isCycleFree	() 					const;			// Verifies whether justification is indeed cycle free, not used, for debugging purposes.

	void	addExternalDisjuncts(const std::set<Var>& ufs, vec<Lit>& loopf);

	// WELL FOUNDED MODEL CHECKING

	/*
	 * Implementation of Tarjan's algorithm for detecting strongly connected components.
	 */
	void visitWF(Var i, std::vector<Var> &root, std::vector<bool> &incomp, std::stack<Var> &stack, std::vector<Var> &visited, int& counter, bool throughPositiveLit, std::vector<int>& rootofmixed);
	/*
	 * Search for mixed cycles in the justification graph of the current model.
	 * @post For every mixed cycle in the justification graph, there is one literal of the cycle on \c _mixedCycleRoots.
	 */
	void findMixedCycles(std::vector<Var> &root, std::vector<int>& rootofmixed);
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
};

}

#endif /* IDSOLVER_H_ */
