/************************************
 DataAndInference.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#pragma once

#include <vector>

#include "Datastructures.hpp"
#include "MXStatistics.hpp"
#include "Options.hpp"
#include <memory>
#include <iostream>

namespace MinisatID {

typedef std::vector<Lit> litlist;

class Translator;
class Remapper;
class Propagator;
class EventQueue;
class PropagatorFactory;
class SearchEngine;
class Optimization;
class PropAndBackMonitor;
class Printer;
class Space;
class ModelManager;

class Task {
private:
	bool terminate;
	SolverOption modes;
public:
	Task(const SolverOption& modes): terminate(false), modes(modes){

	}
	virtual ~Task() {
	}

	virtual void notifyTerminateRequested();
	bool terminateRequested() const {
		return terminate;
	}

	virtual void execute();

protected:
	virtual void innerExecute() = 0;
	const SolverOption& getOptions() const{
		return modes;
	}
};

class SpaceTask: public Task{
	Space* space;
public:
	SpaceTask(Space* space);

	virtual void notifyTerminateRequested();
	virtual void execute();

	Space* getSpace() const {
		return space;
	}

protected:
	SearchEngine& getSolver() const;
};

struct OptimStatement;

enum class MXState {
	MODEL, UNSAT, UNKNOWN
};

class MxWrapper: public SpaceTask {
private:
	ModelExpandOptions _options;
	ModelManager* _solutions;
	Printer* printer;
	litlist assumptions; // TODO remove

public:
	MxWrapper(Space* space, ModelExpandOptions options, const litlist& assumptions);
	~MxWrapper();

	MXStatistics getStats() const;

	/**
	 * NOTE: Returns 0 if an optimization problem where no proven minimal model has been found yet!
	 */
	int getNbModelsFound() const;

	// Note: do not call unless the models are being saved!
	Weight getBestValueFound() const;

	bool isSat() const;
	bool isUnsat() const;
	void notifySolvingAborted();
	litlist getUnsatExplanation() const;

private:
	void innerExecute();

	void notifyCurrentOptimum(const Weight& value) const;

	void addModel(Model* model);

	friend class OneShotUnsatCoreExtraction;
};

class UnitPropagate: public SpaceTask {
private:
	const litlist assumptions;

public:
	UnitPropagate(Space* space, const litlist& assumptions)
			: SpaceTask(space), assumptions(assumptions) {

	}

	literallist getEntailedLiterals() const;
	void writeOutEntailedLiterals();

private:
	void innerExecute();
};

enum class TheoryPrinting { CNF, ECNF, FZ, HUMAN, ECNFGRAPH };

class Transform: public SpaceTask {
private:
	const TheoryPrinting outputlanguage;

public:
	Transform(Space* space, TheoryPrinting outputlanguage)
			: SpaceTask(space), outputlanguage(outputlanguage) {
	}

private:
	void innerExecute();
};

}
