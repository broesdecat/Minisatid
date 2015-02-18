/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <set>
#include <stack>
#include <queue>
#include <vector>
#include <map>
#include <iostream>

#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"
#include "modules/aggsolver/AggProp.hpp"

namespace MinisatID {

struct TempRule;

/**
 * The different possible types of definitions.
 * If a variable is NONDEFALL, no definition is associated with it.
 * If a variable is NONDEFPOS, a definition is associated with it, but there is no recursion through it in the POSITIVE dependency graph
 * 		but there might be recursion over negation (relevant for the well-founded model)
 */
enum class DefType	{ DISJ, CONJ, AGGR };
enum DefOcc 	{ NONDEFOCC, POSLOOP, MIXEDLOOP, BOTHLOOP };
enum UFS 		{ NOTUNFOUNDED, UFSFOUND, STILLPOSSIBLE, OLDCHECK };

class PropRule {
private:
	const Atom head;
	litlist lits;

public:
    PropRule(Lit head, const litlist& ps): head(var(head)), lits(ps){}

    uint 	size() 				const	{ return lits.size(); }
    Lit 	getHead() 			const	{ return mkLit(head, false); }
    Lit 	operator [](int i) 	const	{ return lits[i]; }
    litlist::const_iterator cbegin()	const 	{ return lits.cbegin(); }
    litlist::const_iterator cend()	const 	{ return lits.cend(); }
    const litlist& getBody() const {return lits; }
};

class IDAgg{
private:
	AggBound	bound;
	Lit			head;
	AggSem		sem;
	int			index;
	AggType		type;
	std::vector<WL> wls; // NOTE: SORTED by literal weights!

public:
	IDAgg(const Lit& head, AggBound b, AggSem sem, AggType type, const std::vector<WL>& wls);

	const Lit& 	getHead		() 					const 	{ return head; }
	void	 	setHead		(const Lit& l)			 	{ head = l; }
	int			getIndex	()					const	{ return index; }

	const Weight&	getBound()					const	{ return bound.bound; }
	bool		hasUB		()					const	{ return bound.sign!=AggSign::LB; }
	bool		hasLB		()					const	{ return bound.sign!=AggSign::UB; }
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
	DefinedVar(IDAgg* rule): _definedaggregate(rule), _type(DefType::AGGR), _occ(BOTHLOOP), _isCS(false), _scc(-1){}
	~DefinedVar(){
		if(_type==DefType::AGGR){
			delete(_definedaggregate);
			_definedaggregate = NULL;
		}else{
			delete(_definition);
			_definition = NULL;
		}
	}

	litlist& 		reason(){ return _reason; }
	PropRule* 		definition(){ MAssert(_type!=DefType::AGGR); return _definition; }
	IDAgg* 			definedaggregate(){ MAssert(_type==DefType::AGGR); return _definedaggregate; }
	DefType& 		type(){ return _type; }
	DefOcc& 		occ(){ return _occ; }
	bool &			isCS(){ return _isCS; }
	int &			scc(){ return _scc; }
	litlist& 		justification(){ return _justification; }

	const litlist&	reason()const { return _reason; }
	const DefType&	type()const { return _type; }
	const DefOcc&	occ()const { return _occ; }
	bool			isCS()const { return _isCS; }
	int				scc()const { return _scc; }
	const litlist& 	justification()const { return _justification; }
};

//Statistics
struct IDStats{
    uint64_t cycle_sources, justifiable_cycle_sources, cycles, cycle_sizes, justify_conflicts;
    uint64_t nb_times_findCS, justify_calls, cs_removed_in_justify, succesful_justify_calls, extdisj_sizes, total_marked_size;

    IDStats():
		cycle_sources(0), justifiable_cycle_sources(0), cycles(0), cycle_sizes(0), justify_conflicts(0),
		nb_times_findCS(0), justify_calls(0), cs_removed_in_justify(0), succesful_justify_calls(0),
		extdisj_sizes(0), total_marked_size(0){}

    void print() const{
		std::clog <<"> cycles                : " <<cycles <<"\n";
		std::clog <<"> cycle conflicts       : " <<justify_conflicts <<"\n";
		std::clog <<"> avg cycle size        : " <<(float)cycle_sizes/cycles <<"\n";
		std::clog <<"> avg extdisj size      : " <<(float)extdisj_sizes/cycles <<"\n";
		std::clog <<"> justify runs          : " <<justify_calls <<"(" <<(float)justify_calls/cycles <<"/cycle)\n";
		std::clog <<"> avg. justify searchsp.: " <<(float)total_marked_size/justify_calls <<" lits\n";
		std::clog <<"> cycle sources         : " <<cycle_sources <<"\n";
		std::clog <<">                       : " <<(float)nb_times_findCS/cycle_sources <<" found per run of findCycleSources()\n";
		std::clog <<">                       : " <<(float)cs_removed_in_justify/justify_calls <<" removed per justify run\n";
		std::clog <<">                       : " <<(float)succesful_justify_calls/nb_times_findCS <<" treated per loop\n";
    }
};

class NetworkHandling{
private:
	std::vector<varlist > _occurs;

public:
	NetworkHandling(){}

	const varlist&	occurs		(const Lit& l) const { MAssert(inNetwork(l)); return _occurs[toInt(l)]; }
	varlist&		occurs		(const Lit& l) { MAssert(inNetwork(l)); return _occurs[toInt(l)]; }
	bool 			inNetwork	(const Lit& l) const { return _occurs.size()>(unsigned int)toInt(l); }
	void			add			(const Lit& l, Atom v) { occurs(l).push_back(v); /*MAssert(IDSolver::type(v)==type);*/ }
	void 			resize		(int n) { _occurs.resize(n, varlist()); }
	void 			clear		() { _occurs.clear(); }
};

class IDSolver: public Propagator{
private:
	int definitionID;

	bool needInit;
	DEFFINDCS defn_strategy;

	Atom minvar, nbvars; //The lowest and highest headvariable. INVAR: Definitions will be offset by minvar and the size will be nbvars

	NetworkHandling conj, disj, aggr;

	InterMediateDataStruct*	_seen;

	DEFSEM				sem;
	bool				posrecagg, mixedrecagg;
	bool 				posloops, negloops;

	varlist				sccroots;

	varlist				defdVars;	// All the vars that are the head of some kind of definition (disj, conj or aggr). Allows to iterate over all definitions.
	std::vector<DefinedVar*> definitions; //Maps all variables to NULL or a defined variable

	bool				backtracked;	//True if the solver has backtracked between now and the previous search for cycle sources. Is true at the start
	int64_t				adaption_total;     // Used only if defn_strategy==adaptive. Number of decision levels between indirectPropagate() uses.
	int					adaption_current;   // Used only if defn_strategy==adaptive. Number of decision levels left until next indirectPropagate() use.

	varlist				css; // List of possible support violators.

	std::set<Atom>		savedufs;
	Disjunction			savedloopf;

	IDStats				stats;

public:
	IDSolver(PCSolver* s, int definitionID);
	virtual ~IDSolver();

	// Finding unfounded sets is allowed after adding this set of rules
	void addRuleSet(const std::vector<TempRule*>& rules);
private:
	void addFinishedRule(const TempRule& rule);
	void addFinishedDefinedAggregate(const TempRule& rule);
public:
	virtual void 	accept(ConstraintVisitor& visitor);

	int		getDefinitionID	() const { return definitionID; }
	DEFSEM	getSemantics	() const { return sem; }

	bool	hasRecursiveAggregates	() const 	{ return posrecagg || mixedrecagg; }

	// Propagator methods
	virtual rClause 	getExplanation			(const Lit& l);
	virtual rClause 	notifypropagate			();
	virtual void 		notifyNewDecisionLevel	();
	virtual void 		notifyBacktrack			(int untillevel, const Lit& decision);
	virtual rClause notifyFullAssignmentFound();
	virtual int getNbOfFormulas() const;

	rClause				isWellFoundedModel		();

	bool				isDefined				(Atom var) 	const { return hasDefVar(var); }
	bool 				isConjunctive			(Atom v)		const {	return type(v) == DefType::CONJ; }
	bool 				isDisjunctive			(Atom v) 	const {	return type(v) == DefType::DISJ;	}
	bool 				isDefinedByAggr			(Atom v) 	const {	return type(v) == DefType::AGGR;	}
	const PropRule&		getDefinition			(Atom var) 	const { MAssert(hasDefVar(var)); return *definition(var); }

private:
	void 				initialize				();
	void 				generateSCCs();
	void 				bumpHeadHeuristic();

	void 				addToNetwork(Atom v);

	bool 				loopPossibleOver(Atom v);

	SATVAL 				transformToCNF		(const varlist& sccroots);
	bool 				simplifyGraph		(int& atomsinposloops); //False if problem unsat

	void 				adaptStructsToHead	(Atom head);
	DefinedVar* 		getDefVar			(Atom v) const { MAssert(v>=0 && minvar<=v && v-minvar<nbvars); return definitions[v-minvar]; }
	void				setDefVar			(Atom v, DefinedVar* newvar) { MAssert(v>=0 && minvar<=v && v-minvar<nbvars); definitions[v-minvar] = newvar; }
	bool 				hasDefVar			(Atom v) const { return minvar<=v && v-minvar<nbvars && getDefVar(v)!=NULL; }

	bool 				isDefInPosGraph		(Atom v) const {	return hasDefVar(v) && (occ(v)==POSLOOP || occ(v)==BOTHLOOP); }

	bool 				canBecomeTrue		(Lit l) const { return value(l) != l_False; }
	bool 				inSameSCC			(Atom x, Atom y) const { return isDefined(x) && isDefined(y) && scc(x) == scc(y); }

	litlist& 			reason		(Atom v){ MAssert(hasDefVar(v)); return getDefVar(v)->reason(); }
	PropRule const*		definition	(Atom v) const { MAssert(hasDefVar(v)); return getDefVar(v)->definition(); }
	IDAgg *				aggdefinition(Atom v) const { MAssert(hasDefVar(v)); return getDefVar(v)->definedaggregate(); }
	DefType& 			type		(Atom v){ MAssert(hasDefVar(v)); return getDefVar(v)->type(); }
	DefOcc& 			occ			(Atom v){ MAssert(hasDefVar(v)); return getDefVar(v)->occ(); }
	bool &				isCS		(Atom v){ MAssert(hasDefVar(v)); return getDefVar(v)->isCS(); }
	int &				scc			(Atom v){ MAssert(hasDefVar(v)); return getDefVar(v)->scc(); }
	litlist& 			justification(Atom v){ MAssert(hasDefVar(v)); return getDefVar(v)->justification(); }

	const litlist& 		reason		(Atom v)const { return getDefVar(v)->reason(); }
	const DefType& 		type		(Atom v)const { return getDefVar(v)->type(); }
	const DefOcc& 		occ			(Atom v)const { return getDefVar(v)->occ(); }
	bool 				isCS		(Atom v)const { return getDefVar(v)->isCS(); }
	int 				scc			(Atom v)const { return getDefVar(v)->scc(); }
	const litlist& 		justification(Atom v)const { return getDefVar(v)->justification(); }

	bool				hasSeen		(Atom v) const 	{ return _seen->hasElem(v); }
	int&				seen		(Atom v) 		{ MAssert(hasSeen(v)); return _seen->getElem(v); }
	const int&			seen		(Atom v) const 	{ MAssert(hasSeen(v)); return _seen->getElem(v); }

	void	createDefinition(Atom head, PropRule* r, DefType type);
	void	createDefinition(Atom head, IDAgg* agg);
	void	removeDefinition(Atom head);

	void 	propagateJustificationDisj(const Lit& l, std::vector<litlist>& jstf, litlist& heads);
	void 	propagateJustificationAggr(const Lit& l, std::vector<litlist>& jstf, litlist& heads);
	void 	propagateJustificationConj(const Lit& l, std::queue<Lit>& heads);
	void 	propagateJustificationConj(const Lit& l, litlist& heads);

	void 	findJustificationDisj(Atom v, litlist& jstf);
	bool 	findJustificationDisj(Atom v, litlist& jstf, varlist& nonjstf);
	bool 	findJustificationConj(Atom v, litlist& jstf, varlist& nonjstf);
	bool 	findJustificationAggr(Atom v, litlist& jstf, varlist& nonjstf);

	void 	changejust		(Atom v, litlist& j);

	// Cycle source methods:
	void	addCycleSource				(Atom v);
	void	clearCycleSources			();
	void	findCycleSources			();
	void	findJustification			(Atom v);
	void 	checkJustification			(Atom head);

private:
	bool twovalueddef;
	bool definitionIsTwovalued() const {
		return twovalueddef;
	}
public:

	bool	shouldCheckPropagation();                               // Decide (depending on chosen strategy) whether or not to do propagations now.
	bool	unfounded          (Atom cs, std::set<Atom>& ufs);      // True iff 'cs' is currently in an unfounded set, 'ufs'.
	rClause	assertUnfoundedSet (const std::set<Atom>& ufs);

	void	markNonJustified   			(Atom cs, varlist& tmpseen);                           // Auxiliary for 'unfounded(..)'. Marks all ancestors of 'cs' in sp_justification as 'seen'.
	void	markNonJustifiedAddVar		(Atom v, Atom cs, std::queue<Atom> &q, varlist& tmpseen);
	void	markNonJustifiedAddParents	(Atom x, Atom cs, std::queue<Atom> &q, varlist& tmpseen);
	bool	directlyJustifiable			(Atom v, std::set<Atom>& ufs, std::queue<Atom>& q);            // Auxiliary for 'unfounded(..)'. True if v can be immediately justified by one change_jstfc action.
	bool	isJustified					(const InterMediateDataStruct& currentjust, Lit x) const;
	bool	isJustified					(const InterMediateDataStruct& currentjust, Atom x) const;
	bool 	oppositeIsJustified			(const InterMediateDataStruct& currentjust, const WL& wl, bool real) const;
	bool 	isJustified					(const InterMediateDataStruct& currentjust, const WL& wl, bool real) const;

	bool	propagateJustified			(Atom v, Atom cs, std::set<Atom>& ufs);    // Auxiliary for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified
	void	addLoopfClause				(Lit l, Disjunction& lits);

	void visit(Atom i, std::vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, varlist& roots); // Method to initialize 'scc'.
	void visitFull(Atom i, std::vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, bool throughPositiveLit, varlist& posroots, varlist& rootofmixed, varlist& nodeinmixed);

	void	addExternalDisjuncts(const std::set<Atom>& ufs, litlist& loopf);

	// Debug:
	void 	printPosGraphJustifications() const;
	bool	isCycleFree	() 					const;			// Verifies whether justification is indeed cycle free, not used, for debugging purposes.

	// WELL FOUNDED MODEL CHECKING

	//Well-founded model checking
	bool 				wffixpoint;
	varlist 			wfroot, wfrootnodes;
	std::queue<Lit> 	wfqueue;
	std::set<Atom> 		wfmarkedAtoms;
	std::vector<bool> 	wfisMarked;

	// Implementation of Tarjan's algorithm for detecting strongly connected components.
	void visitWF(Atom i, varlist &root, std::vector<bool> &incomp, std::stack<Atom> &stack, varlist &visited, int& counter, bool throughPositiveLit, std::vector<int>& rootofmixed);
	/*
	 * Search for mixed cycles in the justification graph of the current model.
	 * @post For every mixed cycle in the justification graph, there is one literal of the cycle on \c _mixedCycleRoots.
	 */
	void findMixedCycles(varlist &root, std::vector<int>& rootofmixed);
	// Mark all atoms that are above the mixed cycle roots in the justification graph.
	void markUpward();
	void mark(Atom);
	// For marked literal l, set _counters[l] to the number of marked bodyliterals in its body. When l is conj/disj, and contains an false/true unmarked bodyliteral, l is pushed on _queuePropagate.
	void initializeCounters();
	void forwardPropagate(bool);
	void overestimateCounters();
	void removeMarks();

	// RECURSIVE AGGREGATE SUPPORT
	bool canJustifyHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const;
	bool canJustifyMaxHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const;
	bool canJustifySPHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const;
	IDAgg* getAggDefiningHead(Atom v) const;
	varlist getDefAggHeadsWithBodyLit(Atom x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadBegin(Atom x) const;
	vwl::const_iterator getSetLitsOfAggWithHeadEnd(Atom x) const ;
	void addExternalLiterals(Atom v, const std::set<Atom>& ufs, litlist& loopf, InterMediateDataStruct& seen);
	void findJustificationAggr(Atom head, litlist& outjstf) ;
	bool directlyJustifiable(Atom v, litlist& jstf, varlist& nonjstf, InterMediateDataStruct& currentjust);
	bool isInitiallyJustified(const IDAgg& agg);

	void printRule(Atom var) const;
};

}
