/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <map>
#include <vector>
#include <set>
#include "utils/Utils.hpp"
#include "modules/aggsolver/AggUtils.hpp"
#include "modules/Definition.hpp"

#include "external/ConstraintVisitor.hpp"

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

class LazyTseitinClause;
class LazyGrounder;

class IntView;

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

	void clearStorage(){ // NOTE DANGEROUS!
		storage_ = NULL;
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

	SetWithAggs():set(NULL),type(AggType::CARD){

	}
};

class Factory: public ConstraintVisitor{
public:
	Factory(std::string name): ConstraintVisitor(name){

	}
	virtual SATVAL finish() = 0;
	virtual void includeCPModel(std::vector<VariableEqValue>& varassignments) = 0;
	virtual Lit exists(const CPBinaryRel&) const {
		return mkPosLit(0);
	}

	virtual IntView* getIntView(VarID varID, Weight bound) = 0;
  virtual WLSet* getParsedSet(int id) = 0;
};

class PropagatorFactory:
	public Factory,
	public SATStorage,
	public AggStorage
#ifdef CPSUPPORT
	, public CPStorage
#endif
	{
private:
	PCSolver* engine;

	Definition* definitions;

	std::map<VarID, IntView*> intvars;

	// Parsing support
	std::map<int, SetWithAggs> parsedsets;
	std::vector<Aggregate*> parsedaggs;
	std::vector<LazyTseitinClause*> grounder2clause;

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
	void add(const OptimizeVar& sentence);
	void add(const MinimizeAgg& sentence);
	void add(const BoolVar& object);
	void add(const IntVarEnum& object);
	void add(const IntVarRange& object);
	void add(const CPBinaryRel& object);
	void add(const CPBinaryRelVar& object);
	void add(const CPSumWeighted& object);
	void add(const CPProdWeighted& object);
	void add(const CPAllDiff& object);
	void add(const LazyGroundLit& object);
	void add(const LazyGroundImpl& object);
	void add(const LazyAddition& object);
	void add(const TwoValuedRequirement& object);
	void add(const LazyAtom& object);
	void add(const TwoValuedVarIdRequirement& object);

	SATVAL finish();

	void includeCPModel(std::vector<VariableEqValue>& varassignments);

	template<typename T>
	void notifyMonitorsOfAdding(const T& obj) const;

	virtual IntView* getIntView(VarID varID, Weight bound);

  virtual WLSet* getParsedSet(int id){
    return parsedsets.at(id).set;
  }

private:

	void internalAdd(const Disjunction& sentence);

	bool finishedparsing;
	bool finishedParsing() const {
		return finishedparsing;
	}

	SATVAL finishSet(const WLSet* set, std::vector<TempAgg*>& agg, bool optimagg = false, uint optimpriority = -1);

	template<class Elem>
	Elem createUnconditional(const Elem& obj, Weight neutral);

	template<class Engine>
	void propagateAfterAddition(Engine& engine);
};

}
