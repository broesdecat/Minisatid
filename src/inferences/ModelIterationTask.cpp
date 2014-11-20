/* 
 * File:   ModelIterationTask.cpp
 * Author: rupsbant
 * 
 * Created on November 19, 2014, 6:11 PM
 */

#include "external/ModelIterationTask.hpp"

#include "Printer.hpp"
#include "ModelManager.hpp"
#include "space/Remapper.hpp"
#include "external/Space.hpp"
#include "constraintvisitors/CNFPrinter.hpp"
#include "datastructures/InternalAdd.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "external/Constraints.hpp"

#include "TaskHelpers.hpp"
#include "space/SearchEngine.hpp"

using namespace std;
using namespace MinisatID;

ModelIterationTask::ModelIterationTask(Space* space, ModelExpandOptions options, const litlist& assumptions)
: _options(options),
assumptions(map(assumptions, *space->getRemapper())),
_solutions(new ModelManager(options.savemodels)),
printer(new Printer(_solutions, space, options.printmodels, space->getOptions())) {
}

ModelIterationTask::~ModelIterationTask() {
	delete (_solutions);
	delete (printer);
}

void ModelIterationTask::notifyTerminateRequested() {
	terminate = true;
	space->getEngine()->notifyTerminateRequested();
}

SearchEngine& ModelIterationTask::getSolver() const {
	return *getSpace()->getEngine();
}

/*
 * Possible answers:
 * true => satisfiable, at least one model exists (INDEPENDENT of the number of models requested or found)
 * false => unsatisfiable
 *
 * Possible tasks:
 * do propagation => do not do search, do not save any model
 * check satisfiability => save the first model
 * find n/all models and print them => do not save models, but print them one at a time
 * find n/all models and return them => save all models
 * count the number of models => do not save models
 */
void ModelIterationTask::initialise() {
	space->getEngine()->finishParsing();
	space->notifyInferenceExecuted();

	printer->notifyStartSolving();
	if (getSpace()->isCertainlyUnsat()) {
		_solutions->notifyUnsat();
		printer->notifySolvingFinished();
		return;
	}
	printSearchStart(clog, getOptions().verbosity);
	getSolver().setAssumptions(assumptions);
}

shared_ptr<Model> ModelIterationTask::findNext() {
	std::cerr << "Task\n";
	shared_ptr<Model> ptr = findNextModel();
	if (state != MXState::MODEL) {
		stop();
	}
	return ptr;
}

void ModelIterationTask::stop() {
	if (state == MXState::UNSAT || state == MXState::MODEL_FINAL) {
		if (_solutions->getNbModelsFound() == 0) {
			printNoModels(clog, getOptions().verbosity);
		} else {
			printer->notifyNoMoreModels();
			printNoMoreModels(clog, getOptions().verbosity);
		}
	}
	if (_solutions->getNbModelsFound() == 0) {
		_solutions->notifyUnsat();
		getSpace()->notifyUnsat();
	}
	if (terminateRequested()) {
		printer->notifySolvingAborted();
	} else {
		printer->notifySolvingFinished();
	}
}

MXStatistics ModelIterationTask::getStats() const {
	return getSpace()->getStats();
}

void ModelIterationTask::notifySolvingAborted() {
	printer->notifySolvingAborted();
}

shared_ptr<Model> ModelIterationTask::findNextModel() {
	auto state = getSolver().solve(true);
	if (state == l_Undef || terminateRequested()) {
		this->state = MXState::UNKNOWN;
		return NULL;
	}
	bool modelfound = state == l_True;
	if (not modelfound) {
		this->state = MXState::UNSAT;
		return NULL;
	}
	shared_ptr<Model> model = getSpace()->getEngine()->getModel();
	shared_ptr<Model> ptr = shared_ptr<Model>(createModel(model, *getSpace()->getRemapper()));
	//Invalidate SAT model
	if (!getSolver().moreModelsPossible()) {
		this->state = MXState::MODEL_FINAL;
		return ptr;
	}
	//choices were made, so other models possible
	auto invalidatedState = invalidateModel();
	if (invalidatedState != SATVAL::POS_SAT) {
		this->state = MXState::MODEL_FINAL;
		return ptr;
	}
	this->state = MXState::MODEL;
	return ptr;
}

SATVAL ModelIterationTask::invalidateModel() {
	Disjunction invalidation({});
	getSolver().invalidate(invalidation.literals);
	return invalidateModel(invalidation);
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 * %Ruben Does this ALWAYS return false if UNSAT??
 */
SATVAL ModelIterationTask::invalidateModel(Disjunction& clause) {
	if (getOptions().verbosity >= 3) {
		clog << "Adding model-invalidating clause: [ ";
		clog << getSpace()->toString(clause.literals);
		clog << "]\n";
	}
	internalAdd(clause, getSolver().getBaseTheoryID(), getSolver());
	return getSolver().satState();
}

