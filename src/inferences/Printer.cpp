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
#include "utils/ResourceManager.hpp"
#include "utils/Print.hpp"
#include "utils/TimingUtils.hpp"
#include "ModelManager.hpp"

using namespace std;
using namespace MinisatID;

Printer::Printer(ModelManager* modelmanager, Space* space, Models printoption, const SolverOption& modes) :
		printoption(printoption),
		modelmanager(modelmanager),
		space(space),
		modes(modes),
		optimizing(false), solvingstate(SolvingState::STARTED),
		startfinish(0), endfinish(-1), startsimpl(0), endsimpl(-1), startsolve(0), endsolve(-1){

	resman = std::shared_ptr<ResMan>(new StdMan(false));
}

Printer::~Printer(){
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
	if(startsimpl==0){
		clog <<getStatisticsMessage((endfinish-startfinish), 0, 0);
	}else if(startsolve==0){
		clog <<getStatisticsMessage((endfinish-startfinish), endsimpl-startsimpl, 0);
	}else{
		clog <<getStatisticsMessage(
				(endfinish-startfinish),
				endsimpl-startsimpl,
				endsolve-startsolve);
	}
}

Translator* Printer::getTranslator() const{
	return space->getTranslator();
}

void Printer::notifyCurrentOptimum(const Weight& value) const{
	ostream output(resman->getBuffer());
	getTranslator()->printCurrentOptimum(output, value);
}

void Printer::addModel(Model * const model) {
	ostream output(resman->getBuffer());
	if (getPrintOption() == Models::ALL || (!optimizing && getPrintOption() == Models::BEST)) {
		if (modelmanager->getNbModelsFound() == 1) {
			if (!optimizing && modes.transformat != OutputFormat::ASP) {
				printSatisfiable(output, modes.format, modes.transformat);
				printSatisfiable(clog, modes.format, modes.transformat,	modes.verbosity);
			}
			getTranslator()->printHeader(output);
		}
		getTranslator()->printModel(output, *model); // TODO only prints literals known to the translator, gives strange results sometimes
	}
	if (not optimizing) {
		printNbModels(clog, modelmanager->getNbModelsFound(), modes.verbosity);
	}
}

void Printer::solvingFinished(){
	if(endfinish==-1){
		endfinish = cpuTime();
	}else if(endsimpl==-1){
		endsimpl = cpuTime();
	}else if(endsolve==-1){
		endsolve = cpuTime();
	}

	ostream output(resman->getBuffer());
	if(modelmanager->isUnsat() && getPrintOption()!=Models::NONE){
		printUnSatisfiable(output, modes.format, modes.transformat);
		printUnSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
	}else if(modelmanager->getNbModelsFound()==0 && getPrintOption()!=Models::NONE){
		printUnknown(output, modes.transformat);
	}else{ // not unsat and at least one model
		if(optimizing && getPrintOption()==Models::BEST){
			if(modelmanager->hasOptimalModel()){
				printOptimalModelFound(output, modes.transformat);
			}
			if(modes.format==InputFormat::OPB){
				printSatisfiable(output, modes.format, modes.transformat);
				printSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
			}
			getTranslator()->printModel(output, *modelmanager->getBestModelFound());
		}else if(not optimizing && modes.transformat == OutputFormat::ASP){ // NOTE: Otherwise, SAT is printed BEFORE the first model is printed, so in addModel
			printSatisfiable(output, modes.format, modes.transformat);
			printSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
		}
	}
	output.flush();

	closeOutput();
}

void Printer::closeOutput() {
	if (resman.get() != NULL) {
		resman->close();
	}
}

void Printer::setOutputFile(std::string output){
	if(!output.empty()){
		resman = std::shared_ptr<ResMan>(new FileMan(output.c_str(), true));
	}
}

void Printer::notifySolvingFinished() {
	if(solvingstate == SolvingState::FINISHEDCLEANLY){
		return;
	}else if(solvingstate == SolvingState::ABORTED){
		throw idpexception("System was notified of both ending cleanly and aborting.\n");
	}
	solvingstate = SolvingState::FINISHEDCLEANLY;
	solvingFinished();
}

void Printer::notifySolvingAborted() {
	if(solvingstate == SolvingState::ABORTED){
		return;
	}else if(solvingstate == SolvingState::FINISHEDCLEANLY){
		throw idpexception("System was notified of both ending cleanly and aborting.\n");
	}
	solvingstate = SolvingState::ABORTED;
	solvingFinished();
}
