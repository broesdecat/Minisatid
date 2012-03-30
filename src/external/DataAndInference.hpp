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
#include "satsolver/BasicSATUtils.hpp"
#include <memory>
#include "Space.hpp"
#include <iostream>

namespace MinisatID {

class Translator;
class Remapper;
class Propagator;
class EventQueue;
class PropagatorFactory;
class PCSolver;
class Optimization;
class PropAndBackMonitor;
class InnerModel;
class Printer;
class ModelManager;

class Task {
private:
	bool terminate;
	Space* space;
public:
	Task(Space* space)
			: space(space) {

	}
	virtual ~Task() {
	}

	void notifyTerminateRequested();
	bool terminateRequested() const {
		return terminate;
	}

	void execute();

	Space* getSpace() const {
		return space;
	}

protected:
	virtual void innerExecute() = 0;
	PCSolver& getSolver() const;
	const SolverOption& modes() const;
};

class VarCreation {
private:
	Remapper* remapper;
public:
	VarCreation(Remapper* r)
			: remapper(r) {
	}
	Var createVar();
};

class InnerMonitor {
private:
	Remapper* remapper;
	std::vector<PropAndBackMonitor*> monitors;
public:
	InnerMonitor(Remapper* r)
			: remapper(r) {
	}
	void addMonitor(PropAndBackMonitor* monitor) {
		monitors.push_back(monitor);
	}
	void notifyMonitor(const Lit& propagation, int decisionlevel);
	void notifyMonitor(int untillevel);
};

enum class MXState {
	MODEL, UNSAT, UNKNOWN
};

class ModelExpand: public Task {
private:
	ModelManager* _solutions; // TODO set
	Printer* printer;  // TODO set
	const ModelExpandOptions _options;

	const litlist assumptions;

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

	// TODO is in fact also notifyOptimum?
	void notifyCurrentOptimum(const Weight& value) const;

	void addModel(std::shared_ptr<InnerModel> model);
};

class UnitPropagate: public Task {
private:
	const litlist assumptions;

public:
	UnitPropagate(Space* space, const litlist& assumptions)
			: Task(space), assumptions(assumptions) {

	}

	literallist getEntailedLiterals();
	void writeOutEntailedLiterals();

private:
	void innerExecute();
};

enum class TheoryPrinting { ECNF, FZ, HUMAN, STATS };

class Transform: public Task {
private:
	const TheoryPrinting outputlanguage;
	const std::string filename;
	std::ostream& stream;

public:
	Transform(Space* space, TheoryPrinting outputlanguage, std::string& filename)
			: Task(space), outputlanguage(outputlanguage), filename(filename), stream(std::clog) {
	}
	Transform(Space* space, TheoryPrinting outputlanguage, std::ostream& stream)
			: Task(space), outputlanguage(outputlanguage), filename(""), stream(stream) {
	}

private:
	void innerExecute();
};

// TODO inference: generate unsat core
// => add marker literals to all clauses (only clauses?), solve, analyze, return all their ids
// aggregate => add literal to the set with a weight which can certainly make it true (or always add both weights, then it is certainly correct?
// ids => add literal to all rules which occurs nowhere else

}

#endif /* DATAANDINFERENCE_HPP_ */
