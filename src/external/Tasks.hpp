/************************************
 DataAndInference.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#ifndef DATAANDINFERENCE_HPP_
#define DATAANDINFERENCE_HPP_

#include <vector>

#include "Datastructures.hpp"
#include "Options.hpp"
#include "callback.hpp"
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
	MODEL, UNSAT, UNKNOWN
};

class OptimStatement;

class MXTask: public SpaceTask{
public:
	MXTask(Space* space): SpaceTask(space){}
	virtual bool isSat() const = 0;
	virtual bool isUnsat() const = 0;
	virtual void notifySolvingAborted() = 0;
};

class ModelExpand: public MXTask {
private:
	ModelExpandOptions _options;
	litlist assumptions;
	ModelManager* _solutions;
	Printer* printer;

public:
	ModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions);
	~ModelExpand();

	const modellist& getSolutions() const;
	modellist getBestSolutionsFound() const;

	bool isSat() const;
	bool isUnsat() const;
	void notifySolvingAborted();
	litlist getUnsatExplanation() const;

private:
	void innerExecute();

	int getNbModelsFound() const;
	MXState findNext(const litlist& assmpt, const ModelExpandOptions& options);
	void invalidate(litlist& clause);
	SATVAL invalidateModel(const litlist& clause);

	bool findOptimal(const litlist& assmpt, OptimStatement& optim);
	Weight latestaggoptimum;
	Lit latestlistoptimum;
	int latestsubsetsize;
	litlist savedinvalidation;
	bool invalidateAgg(litlist& invalidation, OptimStatement& optim);
	bool invalidateSubset(litlist& invalidation, litlist& assmpt, OptimStatement& optim);
	bool invalidateValue(litlist& invalidation, OptimStatement& optim);
	void notifyCurrentOptimum(const Weight& value) const;

	void addModel(std::shared_ptr<Model> model);
};

class UnitPropagate: public SpaceTask {
private:
	const litlist assumptions;

public:
	UnitPropagate(Space* space, const litlist& assumptions)
			: SpaceTask(space), assumptions(assumptions) {

	}

	literallist getEntailedLiterals();
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
