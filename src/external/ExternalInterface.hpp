//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

#ifndef EXTERNALINTERFACE_HPP_
#define EXTERNALINTERFACE_HPP_

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <tr1/unordered_map>

#include "external/ExternalUtils.hpp"

#include "theorysolvers/LogicSolver.hpp"
//Have to be included, otherwise this header knows nothing of the inheritance between LogicSolver and its children
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

///////
// External interfaces offered from the solvers
///////

class WrappedLogicSolver{
public:
	//Print statistics of the performed search
	void 	printStatistics	() const;

	//Initialize the datastructures after the full theory has been parsed
	bool 	finishParsing	();

	//Simplify the logical theory. Automatically initializes the datastructures
	bool 	simplify		();

	//Do model expansion, given the options in the solution datastructure.
	//Automatically initializes the datastructures and simplifies the theory
	bool 	solve			(Solution* sol);

	void	setTranslator	(Translator* translator);

protected:
	WrappedLogicSolver			();
	virtual ~WrappedLogicSolver	();

	virtual MinisatID::WLSImpl* getImpl() const = 0;
};

class WrappedPCSolver: public MinisatID::WrappedLogicSolver{
private:
	MinisatID::WPCLSImpl* _impl;

public:
	WrappedPCSolver(const SolverOption& modes);
	~WrappedPCSolver();

	void	addVar			(Atom v);
	bool	addClause		(std::vector<Literal>& lits);
	bool 	addEquivalence	(const Literal& head, const std::vector<Literal>& rightlits, bool conj);
	bool	addRule			(bool conj, Literal head, const std::vector<Literal>& lits);
	bool	addSet			(int id, const std::vector<Literal>& lits);
	bool 	addSet			(int set_id, const std::vector<WLtuple>& lws);
	bool	addSet			(int id, const std::vector<Literal>& lits, const std::vector<Weight>& w);
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
	MinisatID::WPCLSImpl* getImpl() const { return _impl; }
};

class WrappedSOSolver: public MinisatID::WrappedLogicSolver{
private:
	MinisatID::WSOLSImpl* _impl;

public:
	WrappedSOSolver				(const SolverOption& modes);
	virtual ~WrappedSOSolver	();

	//Add information for hierarchy
	bool 	addChild	(vsize parent, vsize child, Literal head);
	bool	addAtoms	(vsize modid, const std::vector<Atom>& atoms);

	//Add information for PC-Solver
	void 	addVar		(vsize modid, Atom v);
	bool 	addClause	(vsize modid, std::vector<Literal>& lits);
	bool 	addRule		(vsize modid, bool conj, Atom head, std::vector<Literal>& lits);
	bool 	addSet		(vsize modid, int set_id, std::vector<WLtuple>& lws);
	bool 	addSet		(vsize modid, int set_id, std::vector<Literal>& lits, std::vector<Weight>& w);
	bool 	addAggrExpr	(vsize modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem);

protected:
	MinisatID::WSOLSImpl* getImpl() const { return _impl; }
};

}

#endif /* EXTERNALINTERFACE_HPP_ */
