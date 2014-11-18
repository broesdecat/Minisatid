/************************************
 DataAndInference.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#ifndef DATAANDINFERENCE_HPP_
#define DATAANDINFERENCE_HPP_

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

enum class MXState {
	MODEL, MODEL_FINAL, UNSAT, UNKNOWN
};

struct OptimStatement;

class ModelExpand: public SpaceTask {
private:
	ModelExpandOptions _options;
protected:
	litlist assumptions; // Note: internal literals
	ModelManager* _solutions;
	Printer* printer;

public:
	ModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions);
	virtual ~ModelExpand();
  
  MXStatistics getStats() const;

	/**
	 * NOTE: Returns 0 if an optimization problem where no proven minimal model has been found yet!
	 */
	int getNbModelsFound() const;

	// Note: do not call unless the models are being saved!
	const modellist& getSolutions() const;
	modellist getBestSolutionsFound() const;
	Weight getBestValueFound() const;

	bool isSat() const;
	bool isUnsat() const;
	void notifySolvingAborted();
	litlist getUnsatExplanation() const;

protected:
	virtual void innerExecute();
  void addModel(std::shared_ptr<Model> model);
  SATVAL invalidateModel();
  SATVAL invalidateModel(Disjunction& clause);      
  bool invalidateAgg(litlist& invalidation, OptimStatement& optim);
	bool invalidateVar(litlist& invalidation, OptimStatement& optim);
	bool invalidateSubset(litlist& invalidation, OptimStatement& optim);
 
private:
	MXState findNext(const litlist& assmpt, const ModelExpandOptions& options);
  MXState findNext();
  
	

	bool findOptimal(const litlist& assmpt, OptimStatement& optim);
	litlist savedinvalidation;

	void notifyCurrentOptimum(const Weight& value) const;

};

class FindModels: public ModelExpand {
private:
  int nbModels;
  
public:
	FindModels(Space* space, ModelExpandOptions opts, const litlist& assumptions); // TODO: pass options by reference
	~FindModels();

protected:
	virtual void innerExecute();
};

class FindOptimalModels: public ModelExpand {
private:
  int nbModels;
  
public:
	FindOptimalModels(Space* space, ModelExpandOptions opts, const litlist& assumptions); // TODO: pass options by reference
	~FindOptimalModels();

protected:
	virtual void innerExecute();
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

#endif /* DATAANDINFERENCE_HPP_ */
