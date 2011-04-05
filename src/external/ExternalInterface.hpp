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

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "external/ExternalUtils.hpp"
#include "external/SolvingMonitor.hpp"

#ifndef __GXX_EXPERIMENTAL_CXX0X__
#include <tr1/memory>
#endif

namespace MinisatID {
class Translator;

class WLSImpl;
class ExternalPCImpl;
class WSOLSImpl;

class Monitor;

class WrappedLogicSolver;
typedef WrappedLogicSolver* pwls;


class WrappedLogicSolver{
public:
	virtual ~WrappedLogicSolver	();

	void 	printStatistics		()	const;

	//Do model expansion, given the options in the solution datastructure.
	//Automatically initializes the datastructures and simplifies the theory.
	void 	solve				(Solution* sol);

	bool 	hasOptimization		() const;

	// Add a monitor, which will be notified when any event happens
	void 	addMonitor(Monitor* const monitor);

protected:
	WrappedLogicSolver			();

	virtual WLSImpl* getImpl	() const = 0;
};

class WrappedPCSolver: public MinisatID::WrappedLogicSolver{
private:
	ExternalPCImpl* impl;

public:
	WrappedPCSolver	(const SolverOption& modes);
	~WrappedPCSolver();

	template<class T>
	bool	add		(const T& sentence);

protected:
	WLSImpl* getImpl() const;
	ExternalPCImpl* getPCImpl() const;
};

// Only those explicitly instantiated (here or elsewhere) will be available in a compiled library
template<> bool WrappedPCSolver::add(const Disjunction& sentence);
template<> bool WrappedPCSolver::add(const DisjunctionRef& sentence);
template<> bool WrappedPCSolver::add(const Equivalence& sentence);
template<> bool WrappedPCSolver::add(const Rule& sentence);
template<> bool WrappedPCSolver::add(const Set& sentence);
template<> bool WrappedPCSolver::add(const WSet& sentence);
template<> bool WrappedPCSolver::add(const WLSet& sentence);
template<> bool WrappedPCSolver::add(const Aggregate& sentence);
template<> bool WrappedPCSolver::add(const MinimizeSubset& sentence);
template<> bool WrappedPCSolver::add(const MinimizeOrderedList& sentence);
template<> bool WrappedPCSolver::add(const MinimizeAgg& sentence);
#ifdef CPSUPPORT
template<> bool WrappedPCSolver::add(const CPIntVar& sentence);
template<> bool WrappedPCSolver::add(const CPBinaryRel& sentence);
template<> bool WrappedPCSolver::add(const CPBinaryRelVar& sentence);
template<> bool WrappedPCSolver::add(const CPSum& sentence);
template<> bool WrappedPCSolver::add(const CPSumWeighted& sentence);
template<> bool WrappedPCSolver::add(const CPSumWithVar& sentence);
template<> bool WrappedPCSolver::add(const CPSumWeightedWithVar& sentence);
template<> bool WrappedPCSolver::add(const CPCount& sentence);
template<> bool WrappedPCSolver::add(const CPAllDiff& sentence);
#endif
template<> bool WrappedPCSolver::add(const ForcedChoices& sentence);

//Second order logic solver
class WrappedSOSolver: public MinisatID::WrappedLogicSolver{
private:
	WSOLSImpl* impl;

public:
	WrappedSOSolver	(const SolverOption& modes);
	virtual ~WrappedSOSolver();

	bool	add		(int modalid, const Disjunction& sentence);
	bool	add		(int modalid, const DisjunctionRef& sentence);
	bool	add		(int modalid, const Rule& sentence);
	bool	add		(int modalid, const Set& sentence);
	bool	add		(int modalid, const WSet& sentence);
	bool	add		(int modalid, const WLSet& sentence);
	bool	add		(int modalid, const Aggregate& sentence);

	bool	add		(int modalid, const RigidAtoms& sentence);
	bool	add		(int modalid, const SubTheory& sentence);

protected:
	WLSImpl* getImpl		() const;
	WSOLSImpl* getSOImpl	() const;
};

}

#endif /* EXTERNALINTERFACE_HPP_ */
