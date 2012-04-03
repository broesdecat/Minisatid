/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_MODELMANAGER_HPP_
#define MINISATID_MODELMANAGER_HPP_

#include <vector>
#include <string>
#include <map>
#include <ostream>
#include <memory>

#include "external/ExternalUtils.hpp"

namespace MinisatID {

class ResMan;

enum class ModelSaved {
	NONE, SAVED, SAVING
};

class ModelManager {
private:
	int nbmodelsfound;
	Model* temporarymodel; //Owning pointer
	modellist models; //IMPORTANT: for optimization problem, models will contain a series of increasingly better models
	//Owning pointer

	bool optimalmodelfound;
	bool unsatfound;

	Models saveoption;
	Models getSaveOption() const {
		return saveoption;
	}

	ModelSaved modelsave; //CRITICAL SECTION SUPPORT

public:
	ModelManager(Models saveoption);
	~ModelManager();

	int getNbModelsFound() const {
		return nbmodelsfound;
	}

	void addModel(Model * const model);
	Model* getBestModelFound() const;
	const modellist& getModels() const {
		return models;
	} //IMPORTANT: no use calling it when models are not being saved.

	bool hasOptimalModel() const {
		return optimalmodelfound;
	}
	void notifyOptimalModelFound() {
		optimalmodelfound = true;
	}

	void notifyUnsat();
	bool isSat() {
		return getNbModelsFound() > 0;
	}
	bool isUnsat() {
		return unsatfound;
	}

private:
	void saveModel(Model * const model);
};

}

#endif /* MINISATID_MODELMANAGER_HPP_ */
