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

namespace MinisatID {

class Translator;
class Remapper;
class Propagator;
class EventQueue;
class PropagatorFactory;
class PCSolver;
class Optimization;
class PropAndBackMonitor;
class Agg;
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

class OptimCreation {
public:
	virtual ~OptimCreation() {
	}
	virtual void addOptimization(Optim type, const litlist& literals) = 0;
	virtual void addAggOptimization(Agg* aggmnmz) = 0;
};

enum class MXState {
	MODEL, UNSAT, UNKNOWN
};

class ModelExpand: public Task, public OptimCreation {
private:
	ModelManager* _solutions; // TODO set
	Printer* printer;  // TODO set
	const ModelExpandOptions _options;

	const litlist assumptions;

	// OPTIMIZATION INFORMATION
	Optim optim;
	Var head;
	std::vector<Lit> to_minimize;
	Agg* agg_to_minimize;

public:
	ModelExpand(Space* space, ModelExpandOptions options, const litlist& assumptions);
	~ModelExpand();

	const modellist& getSolutions() const;

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
	void addOptimization(Optim type, const litlist& literals);
	void addAggOptimization(Agg* aggmnmz);

	PCSolver& getSolver() const;
	const SolverOption& modes() const;

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

	litlist getEntailedLiterals();

private:
	void innerExecute();

	PCSolver& getSolver() const;
	const SolverOption& modes() const;
};

class Transform: public Task {
private:
	const OutputFormat outputlanguage;
	const std::string filename;

public:
	Transform(Space* space, OutputFormat outputlanguage, std::string& filename)
			: Task(space), outputlanguage(outputlanguage), filename(filename) {

	}

private:
	void innerExecute();

	PCSolver& getSolver() const;
	const SolverOption& modes() const;
};

// TODO inference: generate unsat core
// => add marker literals to all clauses (only clauses?), solve, analyze, return all their ids
// aggregate => add literal to the set with a weight which can certainly make it true (or always add both weights, then it is certainly correct?
// ids => add literal to all rules which occurs nowhere else

}

#endif /* DATAANDINFERENCE_HPP_ */
