/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_PRINTER_HPP_
#define MINISATID_PRINTER_HPP_

#include <vector>
#include <string>
#include <map>
#include <ostream>
#include <memory>

#include "external/ExternalUtils.hpp"

namespace MinisatID {

class ResMan;
class ModelManager;
class Space;
class Translator;

enum class SolvingState { STARTED, FINISHEDCLEANLY, ABORTED};

class Printer{
private:
	Models printoption;

        /**
         * ModelManager used for:
         * Counting the number of models.
         * Unsat state: no models have been found total.
         * 
         */
	ModelManager* modelmanager;
        
	Space* space;
	std::shared_ptr<ResMan> resman;
	SolverOption modes;

	bool		optimizing;
	SolvingState solvingstate;

	bool nomoremodels;

	double 	startfinish, endfinish, startsimpl, endsimpl, startsolve, endsolve;

public:
	Printer(ModelManager* modelmanager, Space* translator, Models printoption, const SolverOption& modes);
	~Printer();

	void 	addModel			(Model * const model);

	void 	closeOutput				();
	void 	notifySolvingFinished	();
	void 	notifySolvingAborted	();

	void	notifyOptimizing		() 			{ optimizing = true; }

	void 	notifyNoMoreModels		();

	void notifyStartDataInit		();
	void notifyEndDataInit			();
	void notifyStartSimplifying		();
	void notifyEndSimplifying		();
	void notifyStartSolving			();
	void notifyEndSolving			();

	Translator* getTranslator() const;

	Models getPrintOption() const { return printoption; }

	void notifyCurrentOptimum(const Weight& value) const;

	void printStatistics			() const;

private:
	void 	solvingFinished			();
};

}

#endif /* MINISATID_PRINTER_HPP_ */
