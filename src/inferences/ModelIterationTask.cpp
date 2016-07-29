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
	: modes(space->getOptions()),
	space(space),
	_options(options),
	assumptions(map(assumptions, *space->getRemapper())),
	_solutions(new ModelManager(options.savemodels)),
	printer(new Printer(_solutions, space, options.printmodels, space->getOptions())),
	terminated(false),
	modelsFound(false) {
}

ModelIterationTask::~ModelIterationTask() {
	delete (_solutions);
	delete (printer);
}

void ModelIterationTask::notifyTerminateRequested() {
	terminated = true;
	space->getEngine()->notifyTerminateRequested();
}

SearchEngine& ModelIterationTask::getSolver() const {
	return *getSpace()->getEngine();
}

void ModelIterationTask::addAssumption(Atom l, bool sign) {
	Atom remapped = getSpace()->getRemapper()->getVar(l);
	Lit assump = mkLit(remapped, sign);
	getSolver().addAssumption(assump);
}
void ModelIterationTask::removeAssumption(Atom l, bool sign){
	Atom remapped = getSpace()->getRemapper()->getVar(l);
	Lit assump = mkLit(remapped, sign);
	getSolver().removeAssumption(assump);
	getOutOfUnsat();
}

void ModelIterationTask::addClause(const std::vector<std::pair<unsigned int,bool> >& lits){
  Disjunction disj({});
  for(auto l: lits){
    disj.literals.push_back(mkLit(getSpace()->getRemapper()->getVar(l.first), l.second));
  }
  invalidateModel(disj);
}

void ModelIterationTask::getOutOfUnsat() {
	terminated = false;
	getSolver().getOutOfUnsat();
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
	printer->notifyStartSolving();
	if (getSpace()->isCertainlyUnsat()) {
		printer->notifySolvingFinished();
		return;
	}
	printSearchStart(clog, getOptions().verbosity);
	getSolver().addAssumptions(assumptions);
}

shared_ptr<Model> ModelIterationTask::findNext() {
	if (terminated) {
		return NULL;
	}
	shared_ptr<Model> ptr = findNextModel();
	if (terminated) {
		if (modelsFound) {
			printNoModels(clog, getOptions().verbosity);
		} else {
			printer->notifyNoMoreModels();
			printNoMoreModels(clog, getOptions().verbosity);
		}
	}
	printer->notifySolvingFinished();
	return ptr;
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
		printer->notifySolvingAborted();
		terminated = true;
		return NULL;
	} else if (state == l_False) {
		getSpace()->notifyUnsat();
		printer->notifySolvingFinished();
		terminated = true;
		return NULL;
	}
	shared_ptr<Model> model = getSpace()->getEngine()->getModel();
	shared_ptr<Model> ptr = shared_ptr<Model>(createModel(model, *getSpace()->getRemapper()));
	//Invalidate SAT model
	if (!getSolver().moreModelsPossible()) {
		terminated = true;
		return ptr;
	}
	//choices were made, so other models possible
	auto invalidatedState = invalidateModel();
	if (invalidatedState != SATVAL::POS_SAT) {
		terminated = true;
		return ptr;
	}
	return ptr;
}

SATVAL ModelIterationTask::invalidateModel() {
	Disjunction invalidation({});
	getSolver().invalidate(invalidation.literals);
	return invalidateModel(invalidation);
}

/**
 * Returns false if invalidating the model leads to UNSAT, meaning that no more models are possible. Otherwise true.
 */
SATVAL ModelIterationTask::invalidateModel(Disjunction& clause) {
	if (getOptions().verbosity >= 3) {
		clog << "Adding model(s)-invalidating clause: [ ";
		clog << getSpace()->toString(clause.literals);
		clog << "]\n";
	}
	internalAdd(clause, getSolver().getBaseTheoryID(), getSolver());
	return getSolver().satState();
}

