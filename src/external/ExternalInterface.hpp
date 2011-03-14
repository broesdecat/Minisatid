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

#ifndef __GXX_EXPERIMENTAL_CXX0X__
#include <tr1/memory>
#endif

namespace MinisatID {
class Translator;

class WLSImpl;
class WPCLSImpl;
class WSOLSImpl;

class WrappedLogicSolver;

#ifdef __GXX_EXPERIMENTAL_CXX0X__
typedef std::shared_ptr<WrappedLogicSolver> pwls;
#else
typedef std::tr1::shared_ptr<WrappedLogicSolver> pwls;
#endif


class WrappedLogicSolver{
public:
	void 	printStatistics		()	const;

	//Do model expansion, given the options in the solution datastructure.
	//Automatically initializes the datastructures and simplifies the theory.
	bool 	solve				(Solution* sol);

	bool 	hasOptimization		() const;

	Translator& getTranslator	();
	void	setTranslator		(Translator* translator);

	// Notify the solver a timeout has occurred: allows for finalization time (COMPETITION)
	void	notifyTimeout		()	const;

protected:
	WrappedLogicSolver			();
	virtual ~WrappedLogicSolver	();

	virtual WLSImpl* getImpl	() const = 0;
};

class WrappedPCSolver: public MinisatID::WrappedLogicSolver{
private:
	WPCLSImpl* impl;

public:
	WrappedPCSolver	(const SolverOption& modes);
	~WrappedPCSolver();

	bool	add		(const Disjunction& sentence);
	bool	add		(const DisjunctionRef& sentence);
	bool	add		(const Equivalence& sentence);
	bool	add		(const Rule& sentence);
	bool	add		(const Set& sentence);
	bool	add		(const WSet& sentence);
	bool	add		(const WLSet& sentence);
	bool	add		(const Aggregate& sentence);
	bool	add		(const MinimizeSubset& sentence);
	bool	add		(const MinimizeOrderedList& sentence);
	bool	add		(const MinimizeAgg& sentence);
	bool	add		(const ForcedChoices& sentence);

/*
	bool 	addIntVar		(int groundname, int min, int max);
	bool 	addCPBinaryRel	(const Literal& head, int groundname, EqType rel, int bound);
	bool 	addCPBinaryRelVar(const Literal& head, int groundname, EqType rel, int groundname2);
	bool 	addCPSum		(const Literal& head, const std::vector<int>& termnames, EqType rel, int bound);
	bool 	addCPSum		(const Literal& head, const std::vector<int>& termnames, std::vector<int> mult, EqType rel, int bound);
	bool 	addCPSumVar		(const Literal& head, const std::vector<int>& termnames, EqType rel, int rhstermname);
	bool 	addCPSumVar		(const Literal& head, const std::vector<int>& termnames, std::vector<int> mult, EqType rel, int rhstermname);
	bool 	addCPCount		(const std::vector<int>& termnames, int value, EqType rel, int rhstermname);
	bool 	addCPAlldifferent(const std::vector<int>& termnames);*/

protected:
	WLSImpl* getImpl() const;
	WPCLSImpl* getPCImpl() const;
};

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
