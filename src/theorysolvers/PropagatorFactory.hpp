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

template<class PropStorage>
class ManagedFactoryStorage{
private:
	PropStorage* storage_;

protected:
	ManagedFactoryStorage(): storage_(NULL){}

	void addStorage(PCSolver* engine){
		assert(not hasStorage());
		storage_ = new PropStorage(engine);
	}
	bool hasStorage() const {
		return storage_!=NULL;
	}
	PropStorage* getStorage() const {
		assert(hasStorage());
		return storage_;
	}
};

template<class PropStorage>
class FactoryStorage{
private:
	PropStorage* storage_;

protected:
	FactoryStorage(): storage_(NULL){}

	bool hasStorage() const {
		return storage_!=NULL;
	}
	PropStorage* getStorage() const {
		assert(hasStorage());
		return storage_;
	}

	void setStorage(PropStorage* storage){
		assert(not hasStorage());
		storage_ = storage;
	}
};

typedef FactoryStorage<ModSolver> ModStorage;
typedef FactoryStorage<SATSolver> SATStorage;
#ifdef CPSUPPORT
typedef FactoryStorage<CPSolver> CPStorage;
#endif
typedef ManagedFactoryStorage<SymmetryPropagator<PCSolver*>> SymmStorage;
typedef ManagedFactoryStorage<AggToCNFTransformer> AggStorage;

class PropagatorFactory:
	public ModStorage,
	public SATStorage,
	public SymmStorage,
	public AggStorage
#ifdef CPSUPPORT
	, public CPStorage
#endif
	{
private:
	PCSolver* engine;

	int dummyvar; // dummy, true head
	bool parsing; //state

	std::map<defID, IDSolver*> idsolvers;

	std::map<int, IntVar*> intvars;

	// Parsing support
	int maxset;
	//std::vector<InnerRule*> parsedrules;
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

	void add(const Var& sentence, bool nondecision = false);
	void add(const InnerDisjunction& sentence);
	void add(const InnerEquivalence& sentence);
	void add(const InnerRule& sentence);
	void add(const InnerWLSet& sentence);
	void add(const InnerAggregate& sentence);
	void add(const InnerReifAggregate& sentence);
	void add(const InnerMinimizeSubset& sentence);
	void add(const InnerMinimizeOrderedList& sentence);
	void add(const InnerMinimizeVar& sentence);
	void add(const InnerMinimizeAgg& sentence);
	void add(const InnerForcedChoices& sentence);
	void add(const InnerSymmetryLiterals& sentence);
	void add(const InnerSymmetry& sentence);
	void add(const InnerIntVarEnum& object);
	void add(const InnerIntVarRange& object);
	void add(const InnerCPBinaryRel& object);
	void add(const InnerCPBinaryRelVar& object);
	void add(const InnerCPSumWeighted& object);
	void add(const InnerCPCount& object);
	void add(const InnerCPAllDiff& object);
	void add(const InnerLazyClause& object);

	void add(const std::vector<InnerRule*>& definition);
	void add(InnerDisjunction& disj, rClause& newclause);

	int newSetID();

	SATVAL finishParsing();

	void includeCPModel(std::vector<VariableEqValue>& varassignments);

	void setModSolver(ModSolver* m);

private:
	template<class T>
	void addCP			(const T& formula);

	bool isInitialized	() 	const { return !parsing; }
	bool isParsing		()	const { return parsing; }

	void addVar			(Lit l, bool nondecision = false) { add(var(l), nondecision); }
	void addVars		(const std::vector<Lit>& a);

	void addAggrExpr	(Var headv, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem);

	template<typename T>
	void 		notifyMonitorsOfAdding(const T& obj) const;

	IntVar*		getIntVar(int varID) const;

	SATVAL finishSet(InnerWLSet* set, std::vector<TempAgg*>& agg, bool optimagg = false);
};

}

#endif /* PROPAGATORFACTORY_HPP_ */
