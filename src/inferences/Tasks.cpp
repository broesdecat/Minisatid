/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/Tasks.hpp"

#include "space/Remapper.hpp"
#include "external/Translator.hpp"
#include "space/SearchEngine.hpp"
#include "theorysolvers/PropagatorFactory.hpp"
#include "modules/aggsolver/AggProp.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/IntVar.hpp"
#include "external/SearchMonitor.hpp"
#include "external/FlatZincRewriter.hpp"
#include "external/ECNFPrinter.hpp"
#include "constraintvisitors/CNFPrinter.hpp"
#include "constraintvisitors/ECNFGraphPrinter.hpp"
#include "constraintvisitors/HumanReadableParsingPrinter.hpp"
#include "Printer.hpp"
#include "ModelManager.hpp"
#include "external/utils/ResourceManager.hpp"
#include "external/Space.hpp"
#include "external/Constraints.hpp"
#include "external/Modelexpand.hpp"

#include <map>
#include <vector>

using namespace std;
using namespace MinisatID;

VarID VarCreation::createID() {
	return {remapper->getNewID()};
}

Atom VarCreation::createVar() {
	return remapper->getNewVar();
}

void Task::execute() {
	innerExecute();
}
void SpaceTask::execute() {
	space->getEngine()->finishParsing();
	space->notifyInferenceExecuted();
	Task::execute();
}
void Task::notifyTerminateRequested() {
	terminate = true;
}
void SpaceTask::notifyTerminateRequested() {
	Task::notifyTerminateRequested();
	space->getEngine()->notifyTerminateRequested();
}

SearchEngine& SpaceTask::getSolver() const {
	return *getSpace()->getEngine();
}

SpaceTask::SpaceTask(Space* space)
		: 	Task(space->getOptions()),
			space(space) {

}

// NOTE: EXTERNAL literals
MxWrapper::MxWrapper(Space* space, ModelExpandOptions options, const litlist& assumptions)
		: 	SpaceTask(space),
			_options(options),
			assumptions(map(assumptions, *space->getRemapper())),
			_solutions(new ModelManager(options.savemodels)),
			printer(new Printer(_solutions, space, options.printmodels, space->getOptions())) {

}

MxWrapper::~MxWrapper() {
	delete (_solutions);
	delete (printer);
}

MXStatistics MxWrapper::getStats() const {
	return getSpace()->getStats();
}

int MxWrapper::getNbModelsFound() const {
	if (getSpace()->isOptimizationProblem() && not _solutions->hasOptimalModel()) {
		return 0;
	}
	return _solutions->getNbModelsFound();
}

Weight MxWrapper::getBestValueFound() const {
	if (not getSpace()->isOptimizationProblem()) {
		throw idpexception("Cannot return best models when not doing optimization inference.");
	}
	return _solutions->getBestValueFound();
}

bool MxWrapper::isSat() const {
	return _solutions->isSat();
}
bool MxWrapper::isUnsat() const {
	return _solutions->isUnsat();
}

litlist MxWrapper::getUnsatExplanation() const {
	vector<Lit> outmodel;
	for (auto lit : getSolver().getUnsatExplanation()) {
		if (getSpace()->getRemapper()->wasInput(lit)) {
			outmodel.push_back(getSpace()->getRemapper()->getLiteral(lit));
		}
	}
	return outmodel;
}

void MxWrapper::notifySolvingAborted() {
	printer->notifySolvingAborted();
}

bool findmoreModels(const ModelExpandOptions& options, ModelManager* m) {
	return options.nbmodelstofind == 0 || m->getNbModelsFound() < options.nbmodelstofind;
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
void MxWrapper::innerExecute() {
	printer->notifyStartSolving();
	if (getSpace()->isCertainlyUnsat()) {
		_solutions->notifyUnsat();
		printer->notifySolvingFinished();
		return;
	}

	if (getSpace()->isOptimizationProblem()) {
		printer->notifyOptimizing();
	}

	printSearchStart(clog, getOptions().verbosity);

	auto mx = Modelexpansion(getSpace(), _options, assumptions);

	bool moremodelspossible = true;
	if (getSpace()->isOptimizationProblem()) {
		bool optimumfound = true;
		if (getSpace()->isAlwaysAtOptimum()) {
			auto m = mx.findModel();
			if (m != NULL) {
				addModel(m);
			}
			optimumfound = _solutions->getNbModelsFound() > 0;
		} else {
			while (not mx.optimumFound()) {
				auto m = mx.findBetterModel();
				if (m != NULL) {
					addModel(m);
				}
			}
			optimumfound = true;
		}

		if (optimumfound) {
			_solutions->notifyOptimalModelFound();
			// TODO print optimum found?
		} else {
			moremodelspossible = false;
		}
	}
	if (moremodelspossible) {
		while (findmoreModels(_options, _solutions)) {
			auto m = mx.findModel();
			if (m != NULL) {
				addModel(m);
			} else {
				moremodelspossible = false;
				break;
			}
		}
		if (not moremodelspossible) {
			if (getNbModelsFound() == 0) {
				printNoModels(clog, getOptions().verbosity);
			} else {
				printer->notifyNoMoreModels();
				printNoMoreModels(clog, getOptions().verbosity);
			}
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

void MxWrapper::addModel(Model* model) {
	_solutions->addModel(model);
	printer->addModel(model);
}

void MxWrapper::notifyCurrentOptimum(const Weight& value) const {
	printer->notifyCurrentOptimum(value);
}

void Monitor::notifyMonitor(const Lit& propagation, int decisionlevel) {
	for (auto i = monitors.cbegin(); i < monitors.cend(); ++i) {
		if (remapper->wasInput(propagation)) {
			(*i)->notifyPropagated(remapper->getLiteral(propagation), decisionlevel);
		}
	}
}

void Monitor::notifyMonitor(int untillevel) {
	for (auto i = monitors.cbegin(); i < monitors.cend(); ++i) {
		(*i)->notifyBacktracked(untillevel);
	}
}

literallist UnitPropagate::getEntailedLiterals() const {
	auto lits = getSolver().getEntailedLiterals();
	literallist literals;
	auto r = *getSpace()->getRemapper();
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if (getSolver().rootValue(*i) != l_Undef && r.wasInput(*i)) {
			literals.push_back(r.getLiteral(*i));
		}
	}
	return literals;
}

void UnitPropagate::innerExecute() {
	getSolver().setAssumptions(assumptions);
	getSolver().solve(false);
}

void UnitPropagate::writeOutEntailedLiterals() {
	auto resman = createResMan(getOptions().outputfile);
	ostream output(resman->getBuffer());

	clog << ">>> Following is a list of literals entailed by the theory.\n";
	const auto& lits = getEntailedLiterals();
	bool begin = true;
	for (auto i = lits.cbegin(); i < lits.cend(); ++i) {
		if (not begin) {
			output << " ";
		}
		begin = false;
		output << getSpace()->toString(*i);
	}
	output << "\n";
	resman->close();
}

void Transform::innerExecute() {
	std::shared_ptr<ResMan> resfile(createResMan(getSpace()->getOptions().outputfile));
	ostream output(resfile->getBuffer());
	switch (outputlanguage) {
	case TheoryPrinting::FZ: {
		FlatZincRewriter<ostream> fzrw(getSpace()->getRemapper(), getSpace()->getTranslator(), getOptions(), output);
		getSolver().accept(fzrw);
		break;
	}
	case TheoryPrinting::ECNF: {
		RealECNFPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	case TheoryPrinting::CNF: {
		RealCNFPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	case TheoryPrinting::ECNFGRAPH: {
		ECNFGraphPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	case TheoryPrinting::HUMAN: {
		HumanReadableParsingPrinter<ostream> pr(getSpace()->getEngine(), output);
		getSolver().accept(pr);
		break;
	}
	}
}
