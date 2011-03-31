/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "external/SolvingMonitor.hpp"

#include <vector>
#include <string>
#include <map>
#include <ostream>
#include <iostream>

#include "external/ExternalUtils.hpp"
#include "external/Translator.hpp"
#include "parser/ResourceManager.hpp"
#include "utils/Print.hpp"

#include "GeneralUtils.hpp"

using namespace std;
using namespace MinisatID;
using namespace Print;

Solution::Solution(ModelExpandOptions options) :
		options(options), nbmodelsfound(0),
		optimizing(false), optimalmodelfound(false),
		unsatfound(false),
		modelsave(MODEL_NONE), solvingstate(SOLVING_STARTED),
		owntranslator(new Translator()), translator(owntranslator),
		startparsing(0), endparsing(-1), startfinish(0), endfinish(-1), startsimpl(0), endsimpl(-1), startsolve(0), endsolve(-1){
}

Solution::~Solution(){
	if(owntranslator!=NULL){
		delete owntranslator;
	}
};

void Solution::notifyStartParsing() {
	startparsing = cpuTime();
}
void Solution::notifyEndParsing() {
	endparsing = cpuTime();
}
void Solution::notifyStartDataInit() {
	startfinish = cpuTime();
}
void Solution::notifyEndDataInit() {
	endfinish = cpuTime();
}
void Solution::notifyStartSimplifying() {
	startsimpl = cpuTime();
}
void Solution::notifyEndSimplifying() {
	endsimpl = cpuTime();
}
void Solution::notifyStartSolving() {
	startsolve = cpuTime();
}
void Solution::notifyEndSolving() {
	endsolve = cpuTime();
}

//FIXME what if some was not started
void Solution::printStatistics() const {
	Print::printStatistics(
			(endparsing-startparsing) + (endfinish-startfinish),
			endsimpl-startsimpl,
			endsolve-startsolve
			);
}

const literallist& Solution::getBestModelFound() const {
	assert(modelsave!=MODEL_NONE);
	if (modelsave == MODEL_SAVED) {
		return models.back();
	} else {
		return temporarymodel;
	}
}

void Solution::saveModel(const literallist& model){
	++nbmodelsfound;
	if (modelsave == MODEL_SAVING) { //Error in saving previous model, so abort
		throw idpexception(">> Previous model failed to save, cannot guarantee correctness.\n");
	}
	if (getSaveOption() == SAVE_BEST) {
		if (modelsave != MODEL_NONE) {
			temporarymodel = models.back();
			models.pop_back();
			assert(models.empty());
		}
	}
	modelsave = MODEL_SAVING;
	models.push_back(model);
	modelsave = MODEL_SAVED;
}

void Solution::addModel(const literallist& model) {
	saveModel(model);

	assert(hasTranslator());

	ostream output(resman.get()->getBuffer());
	if (getPrintOption() == PRINT_ALL || (!optimizing && getPrintOption() == PRINT_BEST)) {
		if (getNbModelsFound() == 1) {
			if (!optimizing && modes.transformat != TRANS_ASP) {
				printSatisfiable(output, modes.format, modes.transformat);
				printSatisfiable(clog, modes.format, modes.transformat,	modes.verbosity);
			}
			getTranslator()->printHeader(output);
		}
		getTranslator()->printModel(output, model);
	}
	if (!optimizing) {
		printNbModels(clog, getNbModelsFound(), modes.verbosity);
	}
}

void Solution::solvingFinished(){
	if(endparsing==-1){
		endparsing = cpuTime();
	}else if(endfinish==-1){
		endfinish = cpuTime();
	}else if(endsimpl==-1){
		endsimpl = cpuTime();
	}else if(endsolve==-1){
		endsolve = cpuTime();
	}

	ostream output(resman.get()->getBuffer());
	if(isUnsat()){
		printUnSatisfiable(output, modes.format, modes.transformat);
		printUnSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
	}else if(getNbModelsFound()==0){
		printUnknown(output);
	}else{ // not unsat and at least one model
		if(optimizing && getPrintOption()==PRINT_BEST){
			if(hasOptimalModel()){
				printOptimalModelFound(output, modes.format);
			}
			if(hasTranslator()){
				getTranslator()->printModel(output, getBestModelFound());
			}
		}else if(!optimizing && modes.transformat==TRANS_ASP){
			printSatisfiable(output, modes.format, modes.transformat);
			printSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
		}
	}
}

// FIXME ResMan is not part of the external package (and InterfaceImpl shouldn't be)

void Solution::notifySolvingFinished() {
	if(solvingstate == SOLVING_FINISHEDCLEANLY){
		return;
	}else if(solvingstate == SOLVING_ABORTED){
		throw idpexception("System was notified of both ending cleanly and aborting.\n");
	}
	solvingstate = SOLVING_FINISHEDCLEANLY;
	solvingFinished();
}

void Solution::notifyUnsat() {
	unsatfound = true;
}

void Solution::notifySolvingAborted() {
	if(solvingstate == SOLVING_ABORTED){
		return;
	}else if(solvingstate == SOLVING_FINISHEDCLEANLY){
		throw idpexception("System was notified of both ending cleanly and aborting.\n");
	}
	solvingstate = SOLVING_ABORTED;
	solvingFinished();
}
