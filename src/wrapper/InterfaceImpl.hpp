/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef INTERFACEIMPL_HPP_
#define INTERFACEIMPL_HPP_

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <unordered_map>

#include "external/ExternalUtils.hpp"
#include "external/SolvingMonitor.hpp"

#include "satsolver/BasicSATUtils.hpp"
#include "datastructures/InnerDataStructures.hpp"

namespace MinisatID {

class Translator;
class LogicSolver;
class PCSolver;
class SearchMonitor;
struct InnerModel;
class LazyClauseMonitor;
class LazyClauseRef;

typedef std::vector<Lit> litlist;

// External interfaces offered from the solvers

enum SolverState { INIT, PARSED, SOLVED};
/*
class WrappedSolver{
private:
	SolverState 	state;

public:
	Solution*		solutionmonitor; //Non-owning pointers

public:
	WrappedSolver			(const SolverOption& modes);
	virtual ~WrappedSolver();

	Var 	getNewVar();

	void 	addModel(const InnerModel& model);
	void	notifyOptimalModelFound();

	int		getNbModelsFound() const { return solutionmonitor->getNbModelsFound(); }

	void	setSolutionMonitor	(Solution* sol);

	void 	printLiteral	(std::ostream& stream, const Lit& l) const;
	template<class List>
	void 	printTranslation(std::ostream& output, const List& l){
		std::vector<std::pair<uint, Literal>> litstoprint;
		for(auto i=l.cbegin(); i!=l.cend(); ++i){
			if(canBackMapLiteral(mkPosLit(*i))){
				// TODO NOTE: the theory is printed in the NEW vocabulary, not in the input one
				// So we print the new variable and the translation of its original version
				litstoprint.push_back(std::pair<uint, Literal>(*i, getRemapper()->getLiteral(mkPosLit(*i))));
			}
		}
		getSolMonitor().printTranslation(output, litstoprint);
	}
	void 	printCurrentOptimum(const Weight& value) const;

	SATVAL	getSatState() const;

protected:
	bool	canBackMapLiteral		(const Lit& lit) const;
	Literal getBackMappedLiteral	(const Lit& lit) const;
	std::vector<Literal> getBackMappedModel	(const std::vector<Lit>& model) const;
};

template<>
void WrappedSolver::notifyMonitor(const InnerPropagation& obj);

template<>
void WrappedSolver::notifyMonitor(const InnerBacktrack& obj);
*/
}

#endif /* INTERFACEIMPL_HPP_ */
