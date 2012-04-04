/************************************
 DataAndInference.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#ifndef DATAANDINFERENCE_HPP_
#define DATAANDINFERENCE_HPP_

#include <vector>

#include "external/Datastructures.hpp"
#include "external/Options.hpp"
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
class PCSolver;
class Optimization;
class PropAndBackMonitor;
class Printer;
class Space;
class ModelManager;

class Task {
private:
	bool terminate;
	const SolverOption modes;
public:
	Task(const SolverOption& modes): modes(modes){

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
	PCSolver& getSolver() const;
};

enum class MXState {
	MODEL, UNSAT, UNKNOWN
};

class ModelExpand: public SpaceTask {
private:
	const ModelExpandOptions _options;
	const litlist assumptions;
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

private:
	void innerExecute();

	int getNbModelsFound() const;
	MXState findNext(const litlist& assmpt, const ModelExpandOptions& options);
	void invalidate(litlist& clause);
	SATVAL invalidateModel(const litlist& clause);
	bool invalidateSubset(litlist& invalidation, litlist& assmpt);
	bool invalidateValue(litlist& invalidation);
	void findOptimal(const litlist& assmpt);
	bool invalidateAgg(litlist& invalidation);

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

enum class TheoryPrinting { ECNF, FZ, HUMAN, ECNFGRAPH };

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
