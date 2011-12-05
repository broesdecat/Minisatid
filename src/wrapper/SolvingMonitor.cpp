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
#include "external/ResourceManager.hpp"
#include "utils/Print.hpp"

#include "GeneralUtils.hpp"

using namespace std;
using namespace MinisatID;

Solution::Solution(ModelExpandOptions options) :
		options(options), nbmodelsfound(0),
		temporarymodel(NULL),
		optimizing(false), optimalmodelfound(false),
		unsatfound(false),
		modelsave(MODEL_NONE), solvingstate(SOLVING_STARTED),
		owntranslator(new Translator()), translator(owntranslator),
		startparsing(0), endparsing(-1), startfinish(0), endfinish(-1), startsimpl(0), endsimpl(-1), startsolve(0), endsolve(-1){

	resman = std::shared_ptr<ResMan>(new StdMan(false));
}

Solution::~Solution(){
	if(owntranslator!=NULL){
		delete owntranslator;
	}
	if(temporarymodel!=NULL){
		delete temporarymodel;
	}
	deleteList<Model>(models);
};

Translator* Solution::getTranslator() const {
	return translator;
}
void Solution::setTranslator(Translator* trans) {
	translator = trans ;
}

void Solution::printLiteral(ostream& stream, const Literal& lit) const {
	if(hasTranslator()){
		getTranslator()->printLiteral(stream, lit);
	}
}

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
void Solution::notifyStartSolving() {
	startsolve = cpuTime();
}
void Solution::notifyEndSolving() {
	endsolve = cpuTime();
}

void Solution::printStatistics() const {
	if(startsimpl==0){
		clog <<getStatisticsMessage((endparsing-startparsing) + (endfinish-startfinish), 0, 0);
	}else if(startsolve==0){
		clog <<getStatisticsMessage((endparsing-startparsing) + (endfinish-startfinish), endsimpl-startsimpl, 0);
	}else{
		clog <<getStatisticsMessage(
				(endparsing-startparsing) + (endfinish-startfinish),
				endsimpl-startsimpl,
				endsolve-startsolve);
	}
}

void Solution::notifyCurrentOptimum(const Weight & value) const{
	ostream output(resman->getBuffer());
	getTranslator()->printCurrentOptimum(output, value);
}

const Model& Solution::getBestModelFound() const {
	assert(modelsave!=MODEL_NONE);
	if (modelsave == MODEL_SAVED) {
		return *models.back();
	} else {
		return *temporarymodel;
	}
}

void Solution::saveModel(Model * const model){
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

void Solution::addModel(Model * const model) {
	saveModel(model);

	assert(hasTranslator());

	ostream output(resman->getBuffer());
	if (getPrintOption() == PRINT_ALL || (!optimizing && getPrintOption() == PRINT_BEST)) {
		if (getNbModelsFound() == 1) {
			if (!optimizing && modes.transformat != TRANS_ASP) {
				printSatisfiable(output, modes.format, modes.transformat);
				printSatisfiable(clog, modes.format, modes.transformat,	modes.verbosity);
			}
			getTranslator()->printHeader(output);
		}
		getTranslator()->printModel(output, *model);
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

	ostream output(resman->getBuffer());
	if(isUnsat() && getPrintOption()!=PRINT_NONE){
		printUnSatisfiable(output, modes.format, modes.transformat);
		printUnSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
	}else if(getNbModelsFound()==0 && getPrintOption()!=PRINT_NONE){
		printUnknown(output, modes.transformat);
	}else{ // not unsat and at least one model
		if(optimizing && getPrintOption()==PRINT_BEST){
			if(hasOptimalModel()){
				printOptimalModelFound(output, modes.transformat);
			}
			if(modes.format==FORMAT_OPB){
				printSatisfiable(output, modes.format, modes.transformat);
				printSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
			}
			if(hasTranslator()){
				getTranslator()->printModel(output, getBestModelFound());
			}
		}else if(!optimizing && modes.transformat==TRANS_ASP){
			printSatisfiable(output, modes.format, modes.transformat);
			printSatisfiable(clog, modes.format, modes.transformat, modes.verbosity);
		}
	}
	output.flush();

	closeOutput();
}

void Solution::closeOutput() {
	if (resman.get() != NULL) {
		resman->close();
	}
}

void Solution::setOutputFile(std::string output){
	if(!output.empty()){
		resman = std::shared_ptr<ResMan>(new FileMan(output.c_str(), true));
	}
}

//Only call internally!
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
