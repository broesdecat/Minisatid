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

	/*
	 * Saves the models found.
	 * For optimization problems, as long as optimum has not been proven, it is a list of increasingly better models.
	 * When optimization has been proven, it becomes a list of optimal models.
	 */
	modellist models;
	//Owning pointer

	bool optimalmodelfound;

	Weight latestintoptimum;
	Lit latestlitoptimum; // For ordered litlist optimization

	Models saveoption;
	Models getSaveOption() const {
		return saveoption;
	}

	ModelSaved modelsave; //CRITICAL SECTION SUPPORT

public:
	ModelManager(Models saveoption);
	~ModelManager();

	/**
	 * NOTE: Returns the total number of models found for the theory, NOT considering any optimization statements!!!
	 */
	int getNbModelsFound() const {
		return nbmodelsfound;
	}

	void setLatestOptimum(const Lit& lit){
		latestlitoptimum = lit;
	}
	void setLatestOptimum(const Weight& value){
		latestintoptimum = value;
	}
	Lit getBestLitFound() const{
		return latestlitoptimum;
	}
	Weight getBestValueFound() const {
		return latestintoptimum;
	}

	void addModel(Model * const model);
	modellist getBestModelsFound() const;
	const modellist& getModels() const {
		MAssert(getSaveOption()!=Models::NONE);
		return models;
	}

	bool hasOptimalModel() const {
		return optimalmodelfound;
	}
	void notifyOptimalModelFound();

	bool isSat() {
		return getNbModelsFound() > 0;
	}
	bool isUnsat() {
		return !isSat();
	}

private:
	void saveModel(Model * const model);
};

}

#endif /* MINISATID_MODELMANAGER_HPP_ */
