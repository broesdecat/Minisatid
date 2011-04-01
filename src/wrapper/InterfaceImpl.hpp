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
#include <tr1/unordered_map>

#include "external/ExternalUtils.hpp"
#include "external/SolvingMonitor.hpp"

//IMPORTANT: Need all headers defining an inheritance tree to be able to use their inheritance
#include "theorysolvers/LogicSolver.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/SOSolver.hpp"


namespace MinisatID {

class Translator;
class LogicSolver;
class PCSolver;
class SOSolver;

// External interfaces offered from the solvers

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
	bool 			optimization;
	SolverState 	state;

protected:
	SolverOption	_modes;

public:
	Remapper*		remapper;

	Solution*		solutionmonitor; //Non-owning pointers

public:
	WLSImpl			(const SolverOption& modes);
	virtual ~WLSImpl();

	bool 	hasOptimization	() const { return optimization; }
	void 	solve			();

	void 	addModel		(const vec<Lit>& model);
	void	notifyOptimalModelFound();

	int		getNbModelsFound() { return solutionmonitor->getNbModelsFound(); }

	void	setSolutionMonitor	(Solution* sol);

	const SolverOption& modes()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }
	void 	printStatistics	() const;
	void 	printLiteral	(std::ostream& stream, const Lit& l) const;
	void 	printCurrentOptimum(const Weight& value) const;

protected:
	bool 	finishParsing	();
	bool 	simplify		();

	void	setOptimization	(bool opt) { optimization = opt; }

	virtual MinisatID::LogicSolver* getSolver() const = 0;

	Var 	checkAtom		(const Atom& atom);
	Lit 	checkLit		(const Literal& lit);
	void 	checkLits		(const std::vector<Literal>& lits, vec<Lit>& ll);
	void 	checkLits		(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms		(const std::vector<Atom>& atoms, std::vector<Var>& ll);

	std::streambuf* getRes	() const;

	Remapper*		getRemapper		()	const { return remapper; }

	std::vector<Literal> getBackMappedModel	(const vec<Lit>& model) const;

private:
	Solution& 	getSolMonitor() { return *solutionmonitor; }
	const Solution& getSolMonitor() const { return *solutionmonitor; }
};

class WPCLSImpl: public MinisatID::WLSImpl{
private:
	MinisatID::PCSolver* solver;

public:
	WPCLSImpl		(const SolverOption& modes);
	virtual ~WPCLSImpl();

	bool	add		(const Atom& sentence);
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

protected:
	virtual MinisatID::PCSolver* getSolver() const { return solver; }
};

class WSOLSImpl: public MinisatID::WLSImpl{
private:
	MinisatID::SOSolver* solver;

public:
	WSOLSImpl		(const SolverOption& modes);
	virtual ~WSOLSImpl	();

	bool	add		(int modalid, const Atom& sentence);
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
	virtual MinisatID::SOSolver* getSolver() const { return solver; }
};

}

#endif /* INTERFACEIMPL_HPP_ */
