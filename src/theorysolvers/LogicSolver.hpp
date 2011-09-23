/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SOLVERI_H_
#define SOLVERI_H_

#include <cstdio>

#include "utils/Utils.hpp"

namespace MinisatID {

class Solution;
class WrapperPimpl;

class LogicSolver{
private:
	SolverOption _modes;
	WrapperPimpl& parent;

	//Currently, the monitor is always the parent TODO should add a nice interface for that
	std::vector<WrapperPimpl*> monitors;

public:
	LogicSolver(SolverOption modes, WrapperPimpl& inter)
			: _modes(modes), parent(inter){};
	virtual ~LogicSolver(){};

	virtual void 	finishParsing(bool& unsat) = 0;

	virtual bool	solve(const litlist& assumptions, const ModelExpandOptions& options) = 0;
	virtual void	printTheory(std::ostream& stream) = 0;

			int 	verbosity		() const		{ return modes().verbosity; }
	const SolverOption& modes		() const		{ return _modes; }
			void	setVerbosity	(int verb)		{ _modes.verbosity = verb; }
			void	setNbModels		(int nbmodels)	{ _modes.nbmodels = nbmodels; }

	const WrapperPimpl& getParent	() const	{ return parent; }
	WrapperPimpl& 		getParent	() 			{ return parent; }

	virtual void	notifyNonDecisionVar(Var var) = 0;

	virtual void 	printStatistics	() const = 0;

public:
	void requestMonitor		(WrapperPimpl* monitor) { monitors.push_back(monitor); }
	bool isBeingMonitored	() const { return monitors.size()>0; }
	void notifyMonitor(const InnerPropagation& obj);
	void notifyMonitor(const InnerBacktrack& obj);
};

}

#endif /* SOLVERI_H_ */
