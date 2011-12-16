/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SOLVINGMONITOR_HPP_
#define SOLVINGMONITOR_HPP_

#include <vector>
#include <string>
#include <map>
#include <ostream>

#include "external/ExternalUtils.hpp"
#include "external/Translator.hpp"

namespace MinisatID {

class Translator;
class ResMan;

enum SolvingState { SOLVING_STARTED, SOLVING_FINISHEDCLEANLY, SOLVING_ABORTED};
enum ModelSaved { MODEL_NONE, MODEL_SAVED, MODEL_SAVING };

class Solution{
private:
	ModelExpandOptions options;
	int 		nbmodelsfound;
	Model*		temporarymodel; //Owning pointer
	modellist	models; //IMPORTANT: for optimization problem, models will contain a series of increasingly better models
					//Owning pointer

	literallist assumptions;

	bool		optimizing;
	bool		optimalmodelfound;
	bool		unsatfound;

	ModelSaved modelsave; //CRITICAL SECTION SUPPORT
	SolvingState solvingstate;

	std::shared_ptr<ResMan> resman;

	Translator *owntranslator, *translator;

	SolverOption modes;

	double 		startparsing, endparsing, startfinish, endfinish, startsimpl, endsimpl, startsolve, endsolve;

public:
	Solution(ModelExpandOptions options);
	~Solution();

	void		setModes(SolverOption modes) { this->modes = modes;}
	void 		setInference(Inference inference) { options.search = inference; }

	int 		getNbModelsFound	() const	{ return nbmodelsfound; }
	int 		getNbModelsToFind	() const	{ return options.nbmodelstofind; }
	PrintModel 	getPrintOption		() const 	{ return options.printmodels; }
	SaveModel 	getSaveOption		() const 	{ return options.savemodels; }
	Inference 	getInferenceOption	() const 	{ return options.search; }
	const ModelExpandOptions& getOptions() const { return options; }
	void		setPrintModels		(PrintModel printoption) { options.printmodels = printoption; }
	void		setSaveModels		(SaveModel saveoption)	{ options.savemodels = saveoption; }

	bool		isOptimizationProblem() { return optimizing; }

	const literallist& getAssumptions	() { return assumptions; }

	void 		addModel			(Model * const model);
	const Model&		getBestModelFound	() const;
	const modellist& 	getModels			() const	{ return models; } //IMPORTANT: no use calling it when models are not being saved.

	bool	hasOptimalModel			() const	{ return optimalmodelfound; }
	void	notifyOptimizing		() 			{ optimizing = true; }
	void	notifyOptimalModelFound	()			{ optimalmodelfound = true;	}
	void 	closeOutput				();
	void	setOutputFile			(std::string output);
	void	setNbModelsToFind		(int nb) { options.nbmodelstofind = nb; }
	void 	notifySolvingFinished	();
	void	notifyUnsat				();
	void 	notifySolvingAborted	();

	bool	isSat					() { return getNbModelsFound()>0; }
	bool	isUnsat					() { return unsatfound; }

	void 	setTranslator			(Translator* trans);
	void 	printLiteral			(std::ostream& stream, const Literal& l) const;
	template<class List>
	void 	printTranslation		(std::ostream& output, const List& list) const{
		if(hasTranslator()){
			getTranslator()->printTranslation(output, list);
		}
	}
	void notifyStartParsing			();
	void notifyEndParsing			();
	void notifyStartDataInit		();
	void notifyEndDataInit			();
	void notifyStartSimplifying		();
	void notifyEndSimplifying		();
	void notifyStartSolving			();
	void notifyEndSolving			();

	void notifyCurrentOptimum		(const Weight& w) const;

	void printStatistics			() const;

private:
	bool	hasTranslator			()	const	{ return translator!=NULL; }
	Translator* getTranslator		()	const;

	void 	solvingFinished			();

	void 	saveModel				(Model * const model);
};

}

#endif /* SOLVINGMONITOR_HPP_ */
