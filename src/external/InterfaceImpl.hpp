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

#ifndef INTERFACEIMPL_HPP_
#define INTERFACEIMPL_HPP_

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <tr1/unordered_map>

#include "external/ExternalUtils.hpp"

#include "theorysolvers/LogicSolver.hpp"
#include "theorysolvers/PCSolver.hpp" //IMPORTANT include to show inheritance tree
#include "theorysolvers/SOSolver.hpp"

namespace MinisatID {

class Translator;
class LogicSolver;
class PCSolver;
class SOSolver;

///////
// External interfaces offered from the solvers
///////

enum SolverState { INIT, PARSED, SIMPLIFIED, SOLVED};

typedef std::tr1::unordered_map<int, int> atommap;

class Remapper{
protected:
	int 			maxnumber;

public:
		Remapper(): maxnumber(0){}

	virtual Var		getVar		(const Atom& atom);
	virtual Literal	getLiteral	(const Lit& lit);
	bool			wasInput	(int var)	const { return var<maxnumber; }
};

class SmartRemapper: public Remapper{
private:
	//Maps from NON-INDEXED to INDEXED atoms
	atommap 		origtocontiguousatommapper, contiguoustoorigatommapper;

public:
	Var		getVar		(const Atom& atom);
	Literal	getLiteral	(const Lit& lit);

};

class WLSImpl{
private:
	SolverState 	_state;
	SolverOption	_modes;

	Remapper*		_remapper;
	Translator*		_translator;

public:
			WLSImpl			(const SolverOption& modes);
	virtual ~WLSImpl		();

	bool 	finishParsing	();
	bool 	simplify		();
	bool 	solve			(Solution* sol);
	void 	addModel		(const vec<Lit>& model, Solution* sol, bool optimizing=false, bool optimal=false);

	void	setTranslator	(Translator* translator);

	const SolverOption& modes()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }
	void 	printStatistics	() const;
	void 	printLiteral	(std::ostream& stream, const Lit& l) const;

protected:
	virtual MinisatID::LogicSolver* getSolver() const = 0;

	Var 	checkAtom		(const Atom& atom);
	Lit 	checkLit		(const Literal& lit);
	void 	checkLits		(const std::vector<Literal>& lits, vec<Lit>& ll);
	void 	checkLits		(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms		(const std::vector<Atom>& atoms, std::vector<Var>& ll);

	std::streambuf* getRes	() const;

	Remapper*		getRemapper		()	const { return _remapper; }
	Translator*		getTranslator	()	const { return _translator; }

	std::vector<Literal> getBackMappedModel	(const vec<Lit>& model) const;
};

class WPCLSImpl: public MinisatID::WLSImpl{
private:
	MinisatID::PCSolver* solver;

public:
			WPCLSImpl		(const SolverOption& modes);
	virtual ~WPCLSImpl		();

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
	virtual MinisatID::PCSolver* getSolver() const { return solver; }
};

class WSOLSImpl: public MinisatID::WLSImpl{
private:
	MinisatID::SOSolver* solver;

public:
			WSOLSImpl	(const SolverOption& modes);
	virtual ~WSOLSImpl	();

	//Add information for hierarchy
	bool 	addChild	(vsize parent, vsize child, Literal head);
	bool	addAtoms	(vsize modid, const std::vector<Atom>& atoms);

	//Add information for PC-Solver
	void 	addVar		(vsize modid, Atom v);
	bool 	addClause	(vsize modid, std::vector<Literal>& lits);
	bool 	addRule		(vsize modid, bool conj, Literal head, std::vector<Literal>& lits);
	bool 	addSet		(vsize modid, int set_id, std::vector<WLtuple>& lws);
	bool 	addSet		(vsize modid, int set_id, std::vector<Literal>& lits, std::vector<Weight>& w);
	bool 	addAggrExpr	(vsize modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem);

protected:
	virtual MinisatID::SOSolver* getSolver() const { return solver; }
};

}

#endif /* INTERFACEIMPL_HPP_ */
