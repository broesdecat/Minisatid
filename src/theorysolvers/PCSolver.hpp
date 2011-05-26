/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PCSOLVER_H_
#define PCSOLVER_H_

#include <map>
#include "utils/Utils.hpp"
#include "theorysolvers/LogicSolver.hpp"

namespace MinisatID {

class SolverOption;
class Propagator;

enum Optim { MNMZ, SUBSETMNMZ, AGGMNMZ, NONE }; // Preference minimization, subset minimization, sum minimization

enum TheoryState {THEORY_PARSING, THEORY_INITIALIZED, THEORY_INITIALIZING};

typedef MinisatID::SATSolver SearchEngine;

class PCSolver: public MinisatID::LogicSolver{
private:
	//Search algorithm
	SearchEngine* searchengine;
	SearchEngine& getSearchEngine() { return searchengine; }

	//mapping of boolvarevents to propagators

	//queue of propagators to execute
	EventQueue* queue;
	EventQueue& getEventQueue() { return queue; }

	TheoryState state;
	uint 		nbskipped; //For printing the full and correct trail.
	std::vector<Lit>		initialprops; //IMPORTANT for printing trail, DO NOT CLEAR

	std::vector<Propagator*> propagations;

	// OPTIMIZATION INFORMATION
	Optim 		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	// State saving
	int 				state_savedlevel;
	bool 				state_savingclauses;
	std::vector<rClause> state_savedclauses;

public:
	PCSolver(SolverOption modes, MinisatID::WrapperPimpl& inter);
	virtual ~PCSolver();

	// INIT
	void 	setModSolver	(ModSolver* m);

	Var		newVar	();

	// Solving support
	void 		newDecisionLevel();
	bool 		simplify();
	bool 		solve			(const vec<Lit>& assumptions, const ModelExpandOptions& options);
	lbool 		checkStatus		(lbool status) const;

	Var			changeBranchChoice(const Var& chosenvar);

	bool 		assertedBefore	(const Var& l, const Var& p) const;
	rClause		getExplanation	(Lit l);			//NON-OWNING pointer

	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	rClause 	createClause	(const vec<Lit>& lits, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void 		addLearnedClause(rClause c); 		//Propagate if clause is unit, return false if c is conflicting
	void    	backtrackTo		(int level);		// Backtrack until a certain level.
	void    	setTrue			(Lit p, Propagator* solver, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined

	const vec<Lit>& getTrail	() 		const;
	int 		getStartLastLevel() 	const;
	int 		getLevel		(int var) const; // Returns the decision level at which a variable was deduced.
	int			getCurrentDecisionLevel	() const;
	int			getNbDecisions	() 		const;
	std::vector<Lit> getDecisions() 	const;

	bool 		totalModelFound	(); //cannot be const!

	void		varBumpActivity	(Var v);

	void 		backtrackDecisionLevel(int levels, int untillevel);
	rClause 	propagate		(Lit l);

	// MOD SOLVER support
	void		saveState		();
	void		resetState		();

	// DEBUG
	std::string getModID		() const; // SATsolver asks this to PC such that more info (modal e.g.) can be printed.
	void 		printEnqueued	(const Lit& p) const;
	void		printChoiceMade	(int level, Lit l) const;
	void 		printStatistics	() const;
	void		printState		() const;
	void		printClause		(rClause clause) const;
	void 		printCurrentOptimum(const Weight& value) const;

private:
	int 		getNbModelsFound() const;

	bool		isInitialized	() 	const { return state==THEORY_INITIALIZED; }
	bool		isInitializing	() 	const { return state==THEORY_INITIALIZING; }
	bool		isParsing		()	const { return state==THEORY_PARSING; }

	void		extractLitModel	(InnerModel* fullmodel);
	void		extractVarModel	(InnerModel* fullmodel);

	// SOLVING
	bool 		findNext		(const vec<Lit>& assumpts, const ModelExpandOptions& options);
	bool    	invalidateModel	(InnerDisjunction& clause);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(InnerDisjunction& clause);

	// OPTIMIZATION
    bool 		invalidateValue	(vec<Lit>& invalidation);
	bool 		invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 		findOptimal		(const vec<Lit>& assumps, const ModelExpandOptions& options);
};

}

#endif /* PCSOLVER_H_ */
