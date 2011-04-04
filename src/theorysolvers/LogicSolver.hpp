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
class WLSImpl;

class LogicSolver{
private:
	SolverOption _modes;
	MinisatID::WLSImpl& parent;
	bool hasMonitor;
public:
	LogicSolver(MinisatID::SolverOption modes, MinisatID::WLSImpl& inter)
			:_modes(modes), parent(inter), hasMonitor(false){};
	virtual ~LogicSolver(){};

	virtual bool 	simplify() = 0;
	virtual void 	finishParsing	(bool& present, bool& unsat) = 0;

	virtual bool	solve(const vec<Lit>& assumptions, const ModelExpandOptions& options) = 0;

			int 	verbosity		() const		{ return modes().verbosity; }
	const SolverOption& modes		() const		{ return _modes; }
			void	setVerbosity	(int verb)		{ _modes.verbosity = verb; }
			void	setNbModels		(int nbmodels)	 { _modes.nbmodels = nbmodels; }

	const MinisatID::WLSImpl& 	getParent	() const	{ return parent; }
	MinisatID::WLSImpl& 		getParent	() 			{ return parent; }

	virtual void 	printStatistics	() const = 0;

	void notifyHasMonitor();
	bool isBeingMonitored() const;
	void notifyMonitor(const InnerPropagation& obj);
	void notifyMonitor(const InnerBacktrack& obj);
};



}

#endif /* SOLVERI_H_ */
