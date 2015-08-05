/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "Printer.hpp"

#include <vector>
#include <string>
#include <map>
#include <ostream>
#include <iostream>

#include "external/ExternalUtils.hpp"
#include "external/Translator.hpp"
#include "external/Space.hpp"
#include "external/utils/ResourceManager.hpp"
#include "utils/Print.hpp"
#include "external/utils/TimingUtils.hpp"
#include "ModelManager.hpp"

using namespace std;
using namespace MinisatID;

Printer::Printer(ModelManager* modelmanager, Space* space, Models printoption, const SolverOption& modes)
		: 	printoption(printoption),
			modelmanager(modelmanager),
			space(space),
			modes(modes),
			optimizing(false),
			solvingstate(SolvingState::STARTED),
			nomoremodels(false),
			startfinish(0),
			endfinish(-1),
			startsimpl(0),
			endsimpl(-1),
			startsolve(0),
			endsolve(-1) {
	if (modes.outputfile == "") {
		resman = std::shared_ptr<ResMan>(new StdMan(false));
	} else {
		resman = std::shared_ptr<ResMan>(new FileMan(modes.outputfile, true));
	}
}

Printer::~Printer() {
}

void Printer::notifyStartDataInit() {
	startfinish = cpuTime();
}
void Printer::notifyEndDataInit() {
	endfinish = cpuTime();
}
void Printer::notifyStartSolving() {
	startsolve = cpuTime();
}
void Printer::notifyEndSolving() {
	endsolve = cpuTime();
}

void Printer::printStatistics() const {
	if (startsimpl == 0) {
		clog << getStatisticsMessage((endfinish - startfinish), 0, 0);
	} else if (startsolve == 0) {
		clog << getStatisticsMessage((endfinish - startfinish), endsimpl - startsimpl, 0);
	} else {
		clog << getStatisticsMessage((endfinish - startfinish), endsimpl - startsimpl, endsolve - startsolve);
	}
}

Translator* Printer::getTranslator() const {
	return space->getTranslator();
}

void Printer::notifyCurrentOptimum(const Weight& value) const {
	MAssert(resman.get() != NULL);
	ostream output(resman->getBuffer());
	getTranslator()->printCurrentOptimum(output, value);
}

void Printer::addModel(Model * const model) {
	MAssert(resman.get() != NULL);
	ostream output(resman->getBuffer());
	if (getPrintOption() == Models::ALL || (not optimizing && getPrintOption() == Models::BEST)) {
		if (modelmanager->getNbModelsFound() == 1) {
			if (not optimizing && modes.transformat != OutputFormat::ASP) {
				printSatisfiable(output, modes.transformat);
				printSatisfiable(clog, modes.transformat, modes.verbosity);
			}
			getTranslator()->printHeader(output);
		}
		getTranslator()->printModel(output, *model);
	}
	if (not optimizing) {
		printNbModels(clog, modelmanager->getNbModelsFound(), modes.verbosity);
	}
}

void Printer::solvingFinished() {
	if (endfinish == -1) {
		endfinish = cpuTime();
	} else if (endsimpl == -1) {
		endsimpl = cpuTime();
	} else if (endsolve == -1) {
		endsolve = cpuTime();
	}

	MAssert(resman.get() != NULL);
	ostream output(resman->getBuffer());
	if (solvingstate != SolvingState::ABORTED && modelmanager->isUnsat() && getPrintOption() != Models::NONE) {
		printUnSatisfiable(output, modes.transformat);
		printUnSatisfiable(clog, modes.transformat, modes.verbosity);
	} else if (modelmanager->getNbModelsFound() == 0 && getPrintOption() != Models::NONE) {
		printUnknown(output, modes.transformat);
	} else { // not unsat and at least one model
		if (optimizing && getPrintOption() == Models::BEST) {
			if (modelmanager->hasOptimalModel() && modes.transformat != OutputFormat::ASP && modes.transformat != OutputFormat::FZ) {
				printOptimalModelFound(output, modes.transformat);
			}
			if (modes.format == InputFormat::OPB) {
				printSatisfiable(output, modes.transformat);
				printSatisfiable(clog, modes.transformat, modes.verbosity);
			}
			auto list = modelmanager->getBestModelsFound();
			for (auto i = list.cbegin(); i < list.cend(); ++i) {
				if (modes.transformat == OutputFormat::ASP) {
					printSatisfiable(output, modes.transformat);
					printSatisfiable(clog, modes.transformat, modes.verbosity);
				}
				getTranslator()->printModel(output, **i);
			}
			if (modelmanager->hasOptimalModel() && modes.transformat == OutputFormat::ASP) {
				printOptimalModelFound(output, modes.transformat);
			}
		}

		// NOTE: cannot request multiple optimal models in flatzinc
		if (optimizing && modelmanager->hasOptimalModel() && modes.transformat == OutputFormat::FZ) {
			printOptimalModelFound(output, modes.transformat);
		}else if (nomoremodels) {
			printNoMoreModels(output, modes.transformat);
		}
	}
	output.flush();

	closeOutput();
}

void Printer::closeOutput() {
	if (resman.get() != NULL) {
		resman->close();
		resman.reset();
	}
}

void Printer::notifyNoMoreModels() {
	nomoremodels = true;
}

void Printer::notifySolvingFinished() {
	if (solvingstate == SolvingState::FINISHEDCLEANLY) {
		return;
	} else if (solvingstate == SolvingState::ABORTED) {
		throw idpexception("System was notified of both ending cleanly and aborting.\n");
	}
	solvingstate = SolvingState::FINISHEDCLEANLY;
	solvingFinished();
	printSearchEnd(clog, modes.verbosity);
}

void Printer::notifySolvingAborted() {
	if (solvingstate == SolvingState::ABORTED) {
		return;
	} else if (solvingstate == SolvingState::FINISHEDCLEANLY) {
		throw idpexception("System was notified of both ending cleanly and aborting.\n");
	}
	solvingstate = SolvingState::ABORTED;
	solvingFinished();
	printSearchAborted(clog, modes.verbosity);
}
