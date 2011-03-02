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
#include <tr1/unordered_map>

#include "external/ExternalUtils.hpp"

//IMPORTANT: Need all headers defining an inheritance tree to be able to use their inheritance
#include "theorysolvers/LogicSolver.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/SOSolver.hpp"

#include "external/InterfaceImpl.hpp"

#ifndef __GXX_EXPERIMENTAL_CXX0X__
#include <tr1/memory>
#endif

namespace MinisatID {
class Translator;
class WrappedLogicSolver;

#ifdef __GXX_EXPERIMENTAL_CXX0X__
typedef std::shared_ptr<WrappedLogicSolver> pwls;
#else
typedef std::tr1::shared_ptr<WrappedLogicSolver> pwls;
#endif

class WrappedLogicSolver{
public:
	void 	printStatistics	()	const;

	void	notifyTimeout	()	const;

	//Do model expansion, given the options in the solution datastructure.
	//Automatically initializes the datastructures and simplifies the theory.
	bool 	solve			(Solution* sol);

	bool 	hasOptimization	() const;

	Translator& getTranslator();
	void	setTranslator	(Translator* translator);

protected:
	WrappedLogicSolver			();
	virtual ~WrappedLogicSolver	();

	virtual MinisatID::WLSImpl* getImpl() const = 0;
};

class WrappedPCSolver: public MinisatID::WrappedLogicSolver{
private:
	MinisatID::WPCLSImpl* impl;

public:
	WrappedPCSolver(const SolverOption& modes);
	~WrappedPCSolver();

	void	addVar			(Atom v);

	bool	addClause		(std::vector<Literal>& lits);
	bool 	addEquivalence	(const Literal& head, const std::vector<Literal>& rightlits, bool conj);

	bool	addConjRule		(Atom head, const std::vector<Literal>& lits);
	bool	addDisjRule		(Atom head, const std::vector<Literal>& lits);
	bool	addConjRuleToID (int defid, Atom head, const std::vector<Literal>& lits);
	bool	addDisjRuleToID (int defid, Atom head, const std::vector<Literal>& lits);

	bool	addSet			(int setid, const std::vector<Literal>& lits);
	bool 	addSet			(int setid, const std::vector<WLtuple>& lws);
	bool	addSet			(int setid, const std::vector<Literal>& lits, const std::vector<Weight>& w);
	bool	addAggrExpr		(Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem);

    bool 	addMinimize		(const std::vector<Literal>& lits, bool subsetmnmz);
    bool 	addMinimize		(const Atom head, const int setid, AggType type);

	bool 	addIntVar		(int groundname, int min, int max);
	bool 	addCPBinaryRel	(Literal head, int groundname, EqType rel, int bound);
	bool 	addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2);
	bool 	addCPSum		(Literal head, const std::vector<int>& termnames, EqType rel, int bound);
	bool 	addCPSum		(Literal head, const std::vector<int>& termnames, std::vector<int> mult, EqType rel, int bound);
	bool 	addCPSumVar		(Literal head, const std::vector<int>& termnames, EqType rel, int rhstermname);
	bool 	addCPSumVar		(Literal head, const std::vector<int>& termnames, std::vector<int> mult, EqType rel, int rhstermname);
	bool 	addCPCount		(const std::vector<int>& termnames, int value, EqType rel, int rhstermname);
	bool 	addCPAlldifferent(const std::vector<int>& termnames);

	void	addForcedChoices(const std::vector<Literal> lits);

protected:
	MinisatID::WPCLSImpl* getImpl() const { return impl; }
};

//Second order logic solver
class WrappedSOSolver: public MinisatID::WrappedLogicSolver{
private:
	MinisatID::WSOLSImpl* _impl;

public:
	WrappedSOSolver				(const SolverOption& modes);
	virtual ~WrappedSOSolver	();

	bool 	addSubTheory	(int parent, Literal head, int child);
	bool	addRigidAtoms	(int modid, const std::vector<Atom>& atoms);

	void 	addVar		(int modid, Atom v);
	bool 	addClause	(int modid, std::vector<Literal>& lits);
	bool 	addConjRule	(int modid, Atom head, std::vector<Literal>& lits);
	bool 	addDisjRule	(int modid, Atom head, std::vector<Literal>& lits);
	bool 	addSet		(int modid, int setid, std::vector<WLtuple>& lws);
	bool 	addSet		(int modid, int setid, std::vector<Literal>& lits, std::vector<Weight>& w);
	bool 	addAggrExpr	(int modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem);

protected:
	MinisatID::WSOLSImpl* getImpl() const { return _impl; }
};

}

#endif /* EXTERNALINTERFACE_HPP_ */
