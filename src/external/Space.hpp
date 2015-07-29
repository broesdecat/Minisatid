/************************************
	Space.hpp
	this file belongs to GidL 2.0
	(c) K.U.Leuven
************************************/

#pragma once

#include <vector>
#include "Options.hpp"
#include "LiteralPrinter.hpp"
#include "MXStatistics.hpp"
#include "ConstraintAdditionInterface.hpp"

namespace MinisatID{

class Translator;
class SearchEngine;
class PropAndBackMonitor;
class ModelExpand;

class Monitor {
private:
	Remapper* remapper;
	std::vector<PropAndBackMonitor*> monitors;
public:
	Monitor(Remapper* r)
			: remapper(r) {
	}
	void addMonitor(PropAndBackMonitor* monitor) {
		monitors.push_back(monitor);
	}
	void notifyMonitor(const Lit& propagation, int decisionlevel);
	void notifyMonitor(int untillevel);
	bool hasMonitors() const { return monitors.size()>0; }
};

class VarCreation {
private:
	Remapper* remapper;
public:
	VarCreation(Remapper* r)
			: remapper(r) {
	}
	VarID createID();
	Atom createVar();
};

class Space: public ExternalConstraintVisitor{
private:
	Monitor* monitor;
	VarCreation* varcreator;
	SearchEngine* engine;

public:
	Space(const SolverOption& options, bool oneshot = false); // Set oneshot to true if only one inference will be executed. Code can optimize for this.
	Space(Remapper* remapper, Translator* translator, const SolverOption& options, bool oneshot = false);
	~Space();
	SearchEngine* getEngine() const { return engine; }

	void notifyUnsat();
	bool isCertainlyUnsat() const;

	void 	addMonitor(PropAndBackMonitor* monitor);
  void  finishParsing();

	bool 	isOptimizationProblem() const;

	virtual void add(const Disjunction&);
	virtual void add(const Implication&);
	virtual void add(const Rule&);
	virtual void add(const WLSet&);
	virtual void add(const Aggregate&);
	virtual void add(const MinimizeSubset&);
	virtual void add(const OptimizeVar&);
	virtual void add(const MinimizeAgg&);
	virtual void add(const BoolVar&);
	virtual void add(const IntVarEnum&);
	virtual void add(const IntVarRange&);
	virtual void add(const CPAllDiff&);
	virtual void add(const CPBinaryRel&);
	virtual void add(const CPBinaryRelVar&);
	virtual void add(const CPSumWeighted&);
	virtual void add(const CPProdWeighted&);
	virtual void add(const LazyGroundLit&);
	virtual void add(const LazyGroundImpl&);
	virtual void add(const LazyAddition&);
	virtual void add(const TwoValuedRequirement&);
	virtual void add(const SubTheory&);
	virtual void add(const LazyAtom&);
	virtual void add(const TwoValuedVarIdRequirement& o);

	Value getTruthValue(const Lit& lit) const;

	MXStatistics getStats() const;
  
  ModelExpand* createModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions);
};

}
