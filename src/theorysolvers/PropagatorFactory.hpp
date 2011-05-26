/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PROPAGATORFACTORY_HPP_
#define PROPAGATORFACTORY_HPP_

#include <map>
#include "utils/Utils.hpp"


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

class Propagator;

typedef Minisat::Solver SATSolver;

enum Optim { MNMZ, SUBSETMNMZ, AGGMNMZ, NONE }; // Preference minimization, subset minimization, sum minimization

class PCSolver;

typedef int defID;

class WrappedPropagator{
private:
	Propagator* module;
	const bool createdhere;

	WrappedPropagator(WrappedPropagator&);
	WrappedPropagator& operator=(WrappedPropagator& m);

public:
	bool present; //Indicates whether the solver should be integrated into the search

	WrappedPropagator(Propagator* module, bool createdhere): module(module), createdhere(createdhere), present(true){ assert(module!=NULL);}
	~WrappedPropagator();

	Propagator* get() const { return module; }
};

typedef std::vector<WrappedPropagator*> solverlist;
enum TheoryState {THEORY_PARSING, THEORY_INITIALIZED, THEORY_INITIALIZING};

class PropagatorFactory {
private:
	//OWNING POINTER
	SATSolver* satsolver;

	TheoryState state;
	uint 		nbskipped; //For printing the full and correct trail.
	std::vector<Lit>		initialprops; //IMPORTANT for printing trail, DO NOT CLEAR

	std::vector<Propagator*> propagators;

	// FORCED CHOICES TO MAKE DURING SEARCH
	vec<Lit> forcedchoices;

	// State saving
	int 				state_savedlevel;
	bool 				state_savingclauses;
	std::vector<rClause> state_savedclauses;

	SATSolver* getSolver() const { return satsolver; }

	std::map<defID, WrappedPropagator*> idsolvers;
	bool hasIDSolver(defID id) const;
	void addIDSolver(defID id);
	IDSolver* getIDSolver(defID id) const;
	bool hasPresentIDSolver(defID id) const;

	WrappedPropagator* aggsolver;
	bool hasAggSolver() const;
	void addAggSolver();
	bool hasPresentAggSolver() const;

	WrappedPropagator* modsolver;
	bool hasModSolver() const;
	bool hasPresentModSolver() const;
	ModSolver* getModSolver() const;

	WrappedPropagator* cpsolver;
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
	PropagatorFactory();
	virtual ~PropagatorFactory();

	SATSolver*	getSATSolver() const { return satsolver; }
	AggSolver* getAggSolver() const;

	// INIT
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
	bool	add		(const InnerCPSumWeighted& object);
	bool	add		(const InnerCPCount& object);
	bool	add		(const InnerCPAllDiff& object);

	void		removeAggrHead	(Var head, int defID);
	void		notifyAggrHead	(Var head, int defID);

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

	void		extractLitModel	(InnerModel* fullmodel);
	void		extractVarModel	(InnerModel* fullmodel);
};

}

#endif /* PROPAGATORFACTORY_HPP_ */
