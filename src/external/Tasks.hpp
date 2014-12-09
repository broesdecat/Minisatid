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

	virtual void execute() = 0;

protected:
	const SolverOption& getOptions() const{
		return modes;
	}
};

class SpaceTask: public Task{
protected:
	Space* space;
public:
	SpaceTask(Space* space);

	virtual void notifyTerminateRequested();

	Space* getSpace() const {
		return space;
	}

protected:
	SearchEngine& getSolver() const;
};

struct OptimStatement;

class ModelExpand: public SpaceTask {
private:
	ModelExpandOptions _options;
protected:
	ModelManager* _solutions;
	Printer* printer;

public:
	ModelExpand(Space* space, ModelExpandOptions options);
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
	void addModel(std::shared_ptr<Model> model);
	SATVAL invalidateModel(Disjunction& clause);      
	Lit invalidateAgg(OptimStatement& optim);
	Lit invalidateVar(OptimStatement& optim);
};

class FindModels: public ModelExpand {
private:
  int nbModels;
  
public:
	FindModels(Space* space, ModelExpandOptions opts); // TODO: pass options by reference
	~FindModels();

	virtual void execute();
};

class FindOptimalModels: public ModelExpand {
private:
  int nbModels;
  
public:
	FindOptimalModels(Space* space, ModelExpandOptions opts); // TODO: pass options by reference
	~FindOptimalModels();

	virtual void execute();
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

	virtual void execute();
};

enum class TheoryPrinting { CNF, ECNF, FZ, HUMAN, ECNFGRAPH };

class Transform: public SpaceTask {
private:
	const TheoryPrinting outputlanguage;

public:
	Transform(Space* space, TheoryPrinting outputlanguage)
			: SpaceTask(space), outputlanguage(outputlanguage) {
	}

	virtual void execute();
};

}

#endif /* DATAANDINFERENCE_HPP_ */
