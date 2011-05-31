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
#include <vector>
#include "utils/Utils.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class PCSolver;

class ParsingMonitor;
class SearchMonitor;

class SolverOption;

class Propagator;
class IDSolver;
class AggSolver;
class ModSolver;

#ifdef CPSUPPORT
class CPSolver;
#endif

typedef Minisat::Solver SATSolver;

typedef int defID;

class PropagatorFactory {
private:
	PCSolver* engine;
	PCSolver& getEngine() { return *engine; }
	PCSolver* getEnginep() const { return engine; }
	const PCSolver& getEngine() const { return *engine; }

	bool parsing; //state

	SATSolver* satsolver;
	SATSolver* getSolver() const { return satsolver; }

	std::map<defID, IDSolver*> idsolvers;
	bool hasIDSolver(defID id) const;
	void addIDSolver(defID id);
	IDSolver* getIDSolver(defID id);

	AggSolver* aggsolver;
	bool hasAggSolver() const { return aggsolver!=NULL; }
	void addAggSolver();
	AggSolver* getAggSolver();

	ModSolver* modsolver;
	bool hasModSolver() const { return modsolver!=NULL; }
	ModSolver* getModSolver() const {return modsolver; }


#ifdef CPSUPPORT
	CPSolver* cpsolver;
	bool hasCPSolver() const { return cpsolver!=NULL; }
	CPSolver* getCPSolver();
#else
	bool hasCPSolver() const { return false; }
#endif

	// Logging
	std::vector<ParsingMonitor*> parsingmonitors;

public:
	PropagatorFactory(const SolverOption& modes, PCSolver* engine);
	virtual ~PropagatorFactory();

	bool add(const Var& sentence);
	bool add(const InnerDisjunction& sentence);
	bool add(const InnerEquivalence& sentence);
	bool add(const InnerRule& sentence);
	bool add(const InnerWSet& sentence);
	bool add(const InnerAggregate& sentence);
	bool add(const InnerMinimizeSubset& sentence);
	bool add(const InnerMinimizeOrderedList& sentence);
	bool add(const InnerMinimizeAgg& sentence);
	bool add(const InnerForcedChoices& sentence);
	bool add(const InnerSymmetryLiterals& sentence);
	bool add(const InnerIntVarEnum& object);
	bool add(const InnerIntVarRange& object);
	bool add(const InnerCPBinaryRel& object);
	bool add(const InnerCPBinaryRelVar& object);
	bool add(const InnerCPSumWeighted& object);
	bool add(const InnerCPCount& object);
	bool add(const InnerCPAllDiff& object);

	bool add(InnerDisjunction& disj, rClause& newclause);

	void finishParsing();

	void setModSolver(ModSolver* m);

	//TODO should remove this dependency when possible
	AggSolver* getOptimAggSolver() { return aggsolver; }

private:
	template<class T>
	bool		addCP			(const T& formula);

	bool		isInitialized	() 	const { return !parsing; }
	bool		isParsing		()	const { return parsing; }

	void 		addVar			(Lit l) { add(var(l)); }
	void 		addVars			(const vec<Lit>& a);
	void 		addVars			(const std::vector<Lit>& a);

	template<typename T>
	void 		notifyMonitorsOfAdding(const T& obj) const ;
};

}

#endif /* PROPAGATORFACTORY_HPP_ */
