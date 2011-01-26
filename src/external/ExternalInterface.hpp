//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

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

namespace MinisatID {

class Translator;

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
    bool 	addSumMinimize	(const Atom head, const int setid);

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
