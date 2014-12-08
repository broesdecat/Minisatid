/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "ModelManager.hpp"

#include <vector>
#include <string>
#include <map>
#include <ostream>
#include <iostream>

#include "external/ExternalUtils.hpp"
#include "external/Translator.hpp"
#include "external/utils/ResourceManager.hpp"
#include "utils/Print.hpp"
#include "external/utils/TimingUtils.hpp"

using namespace std;
using namespace MinisatID;

ModelManager::ModelManager(Models saveoption) :
		nbmodelsfound(0), temporarymodel(NULL), optimalmodelfound(false),  saveoption(saveoption), modelsave(ModelSaved::NONE) {
}

ModelManager::~ModelManager() {
	if (temporarymodel != NULL) {
		delete temporarymodel;
	}
	deleteList<Model>(models);
}

void ModelManager::notifyOptimalModelFound() {
	if(optimalmodelfound){
		return;
	}
	optimalmodelfound = true;
	nbmodelsfound = 1;
	auto temp = models.back();
	models.pop_back();
	deleteList<Model>(models);
	models = {temp};
}

modellist ModelManager::getBestModelsFound() const {
	MAssert(modelsave!=ModelSaved::NONE);
	if(optimalmodelfound){
		return models;
	}
	if (modelsave == ModelSaved::SAVED) {
		return {models.back()};
	} else {
		return {temporarymodel};
	}
}

void ModelManager::saveModel(Model * const model) {
	++nbmodelsfound;
	if (modelsave == ModelSaved::SAVING) { //Error in saving previous model, so abort
		throw idpexception(">> Previous model failed to save, cannot guarantee correctness.\n");
	}
	if (getSaveOption() == Models::BEST && not optimalmodelfound) {
		if (modelsave != ModelSaved::NONE) {
			temporarymodel = models.back();
			models.pop_back();
			MAssert(models.empty());
		}
	}
	modelsave = ModelSaved::SAVING;
	models.push_back(model);
	modelsave = ModelSaved::SAVED;
	temporarymodel = NULL;
}

void ModelManager::addModel(Model * const model) {
	saveModel(model);
}
