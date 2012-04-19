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
#include "modules/Definition.hpp"

namespace Minisat{
	class Solver;
}

namespace MinisatID {

class TempAgg;

class IntVar;
class PCSolver;

class ConstraintPrinter;
class SearchMonitor;

class SolverOption;

class Propagator;
class IDSolver;
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
	~ManagedFactoryStorage(){
		resetStorage();
	}

	void resetStorage(){
		if(hasStorage()){
			delete(storage_);
			storage_ = NULL;
		}
	}

	void addStorage(PCSolver* engine){
		MAssert(not hasStorage());
		storage_ = new PropStorage(engine);
	}
	bool hasStorage() const {
		return storage_!=NULL;
	}
	PropStorage* getStorage() const {
		MAssert(hasStorage());
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
		MAssert(hasStorage());
		return storage_;
	}

	void setStorage(PropStorage* storage){
		MAssert(not hasStorage());
		storage_ = storage;
	}
};

typedef FactoryStorage<SATSolver> SATStorage;
#ifdef CPSUPPORT
typedef FactoryStorage<CPSolver> CPStorage;
#endif
typedef ManagedFactoryStorage<AggToCNFTransformer> AggStorage;

struct SetWithAggs{
	WLSet* set;
	std::vector<TempAgg*> aggs;
	AggType type;
};

class PropagatorFactory:
	public SATStorage,
	public AggStorage
#ifdef CPSUPPORT
	, public CPStorage
#endif
	{
private:
	PCSolver* engine;

	Definition* definitions;

	int dummyvar; // dummy, true head

	std::map<int, IntVar*> intvars;

	// Parsing support
	int maxset;
	std::map<int, SetWithAggs> parsedsets;
	std::vector<Aggregate*> parsedaggs;

	// Logging
	std::vector<ConstraintPrinter*> parsingmonitors;

	void guaranteeAtRootLevel();

public:
	PropagatorFactory(const SolverOption& modes, PCSolver* engine);
	virtual ~PropagatorFactory();

	PCSolver& getEngine() { return *engine; }
	PCSolver* getEnginep() const { return engine; }
	const PCSolver& getEngine() const { return *engine; }

	void add(const Disjunction& sentence);
	void add(const Implication& sentence);
	void add(const Rule& sentence);
	void add(const WLSet& sentence);
	void add(const Aggregate& sentence);
	void add(const MinimizeSubset& sentence);
	void add(const MinimizeOrderedList& sentence);
	void add(const MinimizeVar& sentence);
	void add(const MinimizeAgg& sentence);
	void add(const Symmetry& sentence);
	void add(const IntVarEnum& object);
	void add(const IntVarRange& object);
	void add(const CPBinaryRel& object);
	void add(const CPBinaryRelVar& object);
	void add(const CPSumWeighted& object);
	void add(const CPCount& object);
	void add(const CPAllDiff& object);
	void add(const CPElement& object);
	void add(const LazyGroundLit& object);

	int newSetID();

	SATVAL finishParsing();

	void includeCPModel(std::vector<VariableEqValue>& varassignments);

private:
	// NOTE already added literals!
	void addImplication(const Lit& head, const litlist& body, bool conjunction);
	// NOTE already added literals!
	void addReverseImplication(const Lit& head, const litlist& body, bool conjunction);

	template<class T>
	void addCP			(const T& formula);

	void addAggrExpr	(Var headv, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem);

	template<typename T>
	void 		notifyMonitorsOfAdding(const T& obj) const;

	IntVar*		getIntVar(int varID) const;

	bool finishedparsing;
	bool finishedParsing() const {
		return finishedparsing;
	}

	SATVAL finishSet(const WLSet* set, std::vector<TempAgg*>& agg, bool optimagg = false, uint optimpriority = -1);
};

}

#endif /* PROPAGATORFACTORY_HPP_ */
