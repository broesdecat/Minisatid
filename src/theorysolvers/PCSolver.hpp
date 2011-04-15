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

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class ECNFPrinter;

class SolverOption;

class IDSolver;
class AggSolver;
class ModSolver;

#ifdef CPSUPPORT
class CPSolver;
#endif

class DPLLTmodule;

typedef Minisat::Solver SATSolver;

enum Optim { MNMZ, SUBSETMNMZ, AGGMNMZ, NONE }; // Preference minimization, subset minimization, sum minimization

class PCLogger{
private:
	std::vector<int> occurrences;
	int propagations;

public:
	PCLogger();

	void addPropagation() { ++propagations; }
	int getNbPropagations() const { return propagations; }
	void addCount(Var v);
	int getCount(Var v) const;

};

class PCSolver;

typedef int defID;

class DPLLTSolver{
private:
	DPLLTmodule* module;
	const bool createdhere;

	DPLLTSolver(DPLLTSolver&);
	DPLLTSolver& operator=(DPLLTSolver& m);

public:
	bool present; //Indicates whether the solver should be integrated into the search

	DPLLTSolver(DPLLTmodule* module, bool createdhere): module(module), createdhere(createdhere), present(true){ assert(module!=NULL);}
	~DPLLTSolver();

	DPLLTmodule* get() const { return module; }
};

typedef std::vector<DPLLTSolver*> solverlist;
enum TheoryState {THEORY_PARSING, THEORY_INITIALIZED, THEORY_INITIALIZING};

class PCSolver: public MinisatID::LogicSolver{
private:
	//OWNING POINTER
	SATSolver* satsolver;

	// IMPORTANT: implicit invariant that IDsolver is always last in the list!
	solverlist solvers;

	TheoryState state;
	uint 		nbskipped; //For printing the full and correct trail.
	std::vector<Lit>		initialprops; //IMPORTANT for printing trail, DO NOT CLEAR

	std::vector<DPLLTmodule*> propagations;

	// OPTIMIZATION INFORMATION
	Optim 		optim;
	Var 		head;
	vec<Lit>	to_minimize;

	// FORCED CHOICES TO MAKE DURING SEARCH
	vec<Lit> forcedchoices;

	// State saving
	int 				state_savedlevel;
	bool 				state_savingclauses;
	std::vector<rClause> state_savedclauses;

	SATSolver* getSolver() const { return satsolver; }

	std::map<defID, DPLLTSolver*> idsolvers;
	bool hasIDSolver(defID id) const;
	void addIDSolver(defID id);
	IDSolver* getIDSolver(defID id) const;
	bool hasPresentIDSolver(defID id) const;

	DPLLTSolver* aggsolver;
	bool hasAggSolver() const;
	void addAggSolver();
	bool hasPresentAggSolver() const;

	DPLLTSolver* modsolver;
	bool hasModSolver() const;
	bool hasPresentModSolver() const;
	ModSolver* getModSolver() const;

	DPLLTSolver* cpsolver;
	bool hasCPSolver() const;
	bool hasPresentCPSolver() const;

#ifdef CPSUPPORT
	void addCPSolver();
	CPSolver* getCPSolver() const;
#endif

	// Logging
	PCLogger* logger;
	ECNFPrinter* ecnfprinter;
	static bool headerunprinted;

	// Monitoring
	bool	hasMonitor;

public:
	PCSolver(SolverOption modes, MinisatID::WLSImpl& inter);
	virtual ~PCSolver();

	SATSolver*	getSATSolver() const { return satsolver; }
	AggSolver* getAggSolver() const;

	// INIT
	void 	setModSolver	(ModSolver* m);

	Var		newVar	();
	bool	add		(Var v);
	bool	add		(const InnerDisjunction& sentence);
	bool	add		(const InnerEquivalence& sentence);
	bool	add		(const InnerRule& sentence);
	bool	add		(const InnerWSet& sentence);
	bool	add		(const InnerAggregate& sentence);
	bool	add		(const InnerMinimizeSubset& sentence);
	bool	add		(const InnerMinimizeOrderedList& sentence);
	bool	add		(const InnerMinimizeAgg& sentence);
	bool	add		(const InnerForcedChoices& sentence);
	bool	add		(const InnerSymmetryLiterals& sentence);
	bool	add		(const InnerIntVarEnum& object);
	bool	add		(const InnerIntVarRange& object);
	bool	add		(const InnerCPBinaryRel& object);
	bool	add		(const InnerCPBinaryRelVar& object);
	bool	add		(const InnerCPSum& object);
	bool	add		(const InnerCPSumWeighted& object);
	bool	add		(const InnerCPSumWithVar& object);
	bool	add		(const InnerCPSumWeightedWithVar& object);
	bool	add		(const InnerCPCount& object);
	bool	add		(const InnerCPAllDiff& object);

	// Solving support
	void 		newDecisionLevel();
	void 		finishParsing	(bool& unsat);
	bool 		simplify();
	bool 		solve			(const vec<Lit>& assumptions, const ModelExpandOptions& options);
	lbool 		checkStatus		(lbool status) const; //if status==l_True, do wellfoundednesscheck in IDSolver, if not wellfounded, return l_False, otherwise status

	Var			changeBranchChoice(const Var& chosenvar);

	void		removeAggrHead	(Var head, int defID);
	void		notifyAggrHead	(Var head, int defID);

	bool 		assertedBefore	(const Var& l, const Var& p) const;
	rClause		getExplanation	(Lit l);			//NON-OWNING pointer

	lbool		value			(Var x) const;		// The current value of a variable.
	lbool		value			(Lit p) const;		// The current value of a literal.
	uint64_t	nVars			()      const;		// The current number of variables.

	rClause 	createClause	(const vec<Lit>& lits, bool learned);
	//IMPORTANT: The first literal in the clause is the one which can be propagated at moment of derivation!
	void 		addLearnedClause(rClause c); 		//Propagate if clause is unit, return false if c is conflicting
	void    	backtrackTo		(int level);		// Backtrack until a certain level.
	void    	setTrue			(Lit p, DPLLTmodule* solver, rClause c = nullPtrClause);		// Enqueue a literal. Assumes value of literal is undefined

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
	rClause 	propagateAtEndOfQueue();

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

	// MONITORING
	const PCLogger& getLogger() const { return *logger; }

private:
	template<class T>
	bool		addCP			(const T& formula);

	bool		isInitialized	() 	const { return state==THEORY_INITIALIZED; }
	bool		isInitializing	() 	const { return state==THEORY_INITIALIZING; }
	bool		isParsing		()	const { return state==THEORY_PARSING; }

	bool		hasECNFPrinter	() const { return ecnfprinter!=NULL; }
	ECNFPrinter& getECNFPrinter	() { return *ecnfprinter; }

	const solverlist& getSolvers() const { return solvers; }

	bool		add				(InnerDisjunction& sentence, rClause& newclause);
	void 		addVar			(Lit l) { add(var(l)); }
	void 		addVars			(const vec<Lit>& a);
	void 		addVars			(const std::vector<Lit>& a);

	// SOLVING
	void 		findNext		(const vec<Lit>& assumpts, InnerModel* model, bool& moremodels, const ModelExpandOptions& options);
	bool    	invalidateModel	(InnerDisjunction& clause);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 		invalidate		(InnerDisjunction& clause);
	bool 		findModel		(const vec<Lit>& assumps, vec<Lit>& m, bool& moremodels);

	// OPTIMIZATION
    bool 		invalidateValue	(vec<Lit>& invalidation);
	bool 		invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 		findOptimal		(const vec<Lit>& assumps, InnerModel* m, const ModelExpandOptions& options);

	bool		foundAtomModel	(InnerModel* partialmodel, const ModelExpandOptions& options);
};

}

#endif /* PCSOLVER_H_ */
