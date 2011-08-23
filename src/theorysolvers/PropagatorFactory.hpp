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
#include <set>
#include "utils/Utils.hpp"
#include "modules/aggsolver/AggUtils.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class TempAgg;

class IntVar;
class PCSolver;

class ParsingMonitor;
class SearchMonitor;

class SolverOption;

class Propagator;
class IDSolver;
class ModSolver;
template<class Solver> class SymmetryPropagator;
class AggToCNFTransformer;

#ifdef CPSUPPORT
class CPSolver;
#endif

typedef Minisat::Solver SATSolver;

typedef int defID;

class PropagatorFactory {
private:
	PCSolver* engine;

	int dummyvar; // dummy, true head
	bool parsing; //state

	SATSolver* satsolver;
	SATSolver* getSolver() const { return satsolver; }

	std::map<defID, IDSolver*> idsolvers;

	ModSolver* modsolver;
	bool hasModSolver() const { return modsolver!=NULL; }
	ModSolver* getModSolver() const {return modsolver; }

	SymmetryPropagator<PCSolver*>* symmsolver;
	void addSymmSolver();
	bool hasSymmSolver() const;
	SymmetryPropagator<PCSolver*>* getSymmSolver() const;

	AggToCNFTransformer* aggToCNF;
	void addAggToCNFTransformer();
	bool hasAggToCNFTransformer() const;
	AggToCNFTransformer* getAggToCNFTransformer() const;

#ifdef CPSUPPORT
	CPSolver* cpsolver;
	bool hasCPSolver() const { return cpsolver!=NULL; }
	CPSolver* getCPSolver();
#else
	bool hasCPSolver() const { return false; }
#endif

	std::map<int, IntVar*> intvars;

	// Parsing support
	int maxset;
	std::vector<InnerRule*> parsedrules;
	typedef std::pair<InnerWLSet*, std::vector<TempAgg*> > SetWithAggs;
	std::map<int, SetWithAggs> parsedsets;
	std::vector<InnerAggregate*> parsedaggs;

	// Logging
	std::vector<ParsingMonitor*> parsingmonitors;

public:
	PropagatorFactory(const SolverOption& modes, PCSolver* engine);
	virtual ~PropagatorFactory();

	bool hasIDSolver(defID id) const;
	void addIDSolver(defID id);
	IDSolver* getIDSolver(defID id);

	PCSolver& getEngine() { return *engine; }
	PCSolver* getEnginep() const { return engine; }
	const PCSolver& getEngine() const { return *engine; }

	bool add(const Var& sentence);
	bool add(const InnerDisjunction& sentence);
	bool add(const InnerEquivalence& sentence);
	bool add(const InnerRule& sentence);
	bool add(const InnerSet& sentence);
	bool add(const InnerWSet& sentence);
	bool add(const InnerWLSet& sentence);
	bool add(const InnerAggregate& sentence);
	bool add(const InnerReifAggregate& sentence);
	bool add(const InnerMinimizeSubset& sentence);
	bool add(const InnerMinimizeOrderedList& sentence);
	bool add(const InnerMinimizeVar& sentence);
	bool add(const InnerForcedChoices& sentence);
	bool add(const InnerSymmetryLiterals& sentence);
	bool add(const InnerSymmetry& sentence);
	bool add(const InnerIntVarEnum& object);
	bool add(const InnerIntVarRange& object);
	bool add(const InnerCPBinaryRel& object);
	bool add(const InnerCPBinaryRelVar& object);
	bool add(const InnerCPSumWeighted& object);
	bool add(const InnerCPCount& object);
	bool add(const InnerCPAllDiff& object);
	bool add(const InnerLazyClause& object);
	bool add(const InnerLazyClauseAddition& object);

	bool add(InnerDisjunction& disj, rClause& newclause);

	int newSetID();

	bool finishParsing();

	void includeCPModel(std::vector<VariableEqValue>& varassignments);

	void setModSolver(ModSolver* m);

private:
	template<class T>
	bool addCP			(const T& formula);

	bool isInitialized	() 	const { return !parsing; }
	bool isParsing		()	const { return parsing; }

	void addVar			(Lit l) { add(var(l)); }
	void addVars		(const vec<Lit>& a);
	void addVars		(const std::vector<Lit>& a);

	bool addAggrExpr	(Var headv, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem);

	template<typename T>
	void 		notifyMonitorsOfAdding(const T& obj) const;

	IntVar*		getIntVar(int varID) const;

	bool finishSet(InnerWLSet* set, std::vector<TempAgg*>& agg);
};

}

#endif /* PROPAGATORFACTORY_HPP_ */
