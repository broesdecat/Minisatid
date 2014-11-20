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

MXStatistics ModelIterationTask::getStats() const{
	return getSpace()->getStats();
}

bool ModelIterationTask::isSat() const {
	return _solutions->isSat();
}
bool ModelIterationTask::isUnsat() const {
	return _solutions->isUnsat();
}

void ModelIterationTask::notifySolvingAborted() {
	printer->notifySolvingAborted();
}


MXState ModelIterationTask::findNext() {
	auto state = getSolver().solve(true);
	if (state == l_Undef || terminateRequested()) {
		return MXState::UNKNOWN;
	}
	bool modelfound = state == l_True;
	if (not modelfound) {
		return MXState::UNSAT;
	}
	shared_ptr<Model> model = getSpace()->getEngine()->getModel();
	shared_ptr<Model> ptr = shared_ptr<Model>(createModel(model, *getSpace()->getRemapper()));
	//Invalidate SAT model
	if (!getSolver().moreModelsPossible()) {
		return MXState::MODEL_FINAL;
	}
	//choices were made, so other models possible
	auto invalidatedState = invalidateModel();
	if(invalidatedState != SATVAL::POS_SAT){
		return MXState::MODEL_FINAL;
	}
	return MXState::MODEL;
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

