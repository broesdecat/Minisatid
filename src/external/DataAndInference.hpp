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

namespace MinisatID{

class Translator;
class Remapper;
class Propagator;
class EventQueue;
class PropagatorFactory;
class PCSolver;
class Optimization;
class Solution;
class PropAndBackMonitor;
class Agg;
class InnerModel;

class Task{
private:
	bool terminate;
	Space* space;
public:
	Task(Space* space): space(space){

	}
	void resetTerminationFlag(){
		terminate = false;
	}
	void notifyTerminateRequested();

	bool terminateRequested() const{
		return terminate;
	}

	void execute();

	virtual void innerExecute() = 0;

	Space* getSpace() const { return space; }
};

class VarCreation{
private:
	Remapper* remapper;
public:
	VarCreation(Remapper* r): remapper(r){}
	Var createVar();
};

class InnerMonitor{
private:
	Remapper* remapper;
	std::vector<PropAndBackMonitor*> monitors;
public:
	InnerMonitor(Remapper* r): remapper(r){}
	void addMonitor(PropAndBackMonitor* monitor){
		monitors.push_back(monitor);
	}
	void notifyMonitor(const Lit& propagation, int decisionlevel);
	void notifyMonitor(int untillevel);
};

class OptimCreation{
public:
	virtual void addOptimization(Optim type, const litlist& literals) = 0;
	virtual void addAggOptimization(Agg* aggmnmz) = 0;
};

enum class MXState { MODEL, UNSAT, UNKNOWN };

class ModelExpand: public Task, public OptimCreation{
private:
	Solution* _solutions;
	ModelExpandOptions _options;

	litlist assumptions;

	// OPTIMIZATION INFORMATION
	Optim optim;
	Var head;
	std::vector<Lit> to_minimize;
	Agg* agg_to_minimize;

public:
	ModelExpand(Space* space, ModelExpandOptions options): Task(space), _options(options){
		// TODO create rest
	}
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
	void printCurrentOptimum(const Weight& value) const;

	void addModel(std::shared_ptr<InnerModel> model);

	Solution* getSolutions() const { return _solutions; }
};

}

#endif /* DATAANDINFERENCE_HPP_ */
