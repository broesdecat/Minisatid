/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef EXTERNALINTERFACE_HPP_
#define EXTERNALINTERFACE_HPP_

#include <cstdlib>
#include <cstdint>
#include <cstdio>

#include "external/ExternalUtils.hpp"
#include "external/SolvingMonitor.hpp"

namespace MinisatID {
class Translator;

class WrapperPimpl;
class PCWrapperPimpl;
class SOWrapperPimpl;

class SearchMonitor;

class LazyClauseMonitor;
class LazyClauseRef;

class WrappedLogicSolver;
typedef WrappedLogicSolver* pwls;


class WrappedLogicSolver{
public:
	virtual ~WrappedLogicSolver	();

	void 	printStatistics		()	const;

	//Do model expansion, given the options in the solution datastructure.
	//Automatically initializes the datastructures and simplifies the theory.
	void 	solve				(Solution* sol);
	void 	printTheory			(std::ostream& stream, Solution* sol) const;

	bool 	hasOptimization		() const;

	// Add a monitor, which will be notified when any event happens
	void 	addMonitor(SearchMonitor* const monitor);

protected:
	WrappedLogicSolver			();

	virtual WrapperPimpl* getImpl	() const = 0;
};

class WrappedPCSolver: public MinisatID::WrappedLogicSolver{
private:
	PCWrapperPimpl* impl;

public:
	WrappedPCSolver	(const SolverOption& modes);
	virtual ~WrappedPCSolver();

	template<class T>
	SATVAL	add(const T& sentence);

protected:
	WrapperPimpl* getImpl() const;
	PCWrapperPimpl* getPCImpl() const;
};

//Second order logic solver
class WrappedSOSolver: public MinisatID::WrappedLogicSolver{
private:
	SOWrapperPimpl* impl;

public:
	WrappedSOSolver	(const SolverOption& modes);
	virtual ~WrappedSOSolver();

	template<class T>
	SATVAL	add		(int modid, const T& sentence);

protected:
	WrapperPimpl* getImpl		() const;
	SOWrapperPimpl* getSOImpl	() const;
};

}

#endif /* EXTERNALINTERFACE_HPP_ */
