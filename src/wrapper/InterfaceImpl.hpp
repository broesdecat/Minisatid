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
class Monitor;
class InnerModel;

// External interfaces offered from the solvers

enum SolverState { INIT, PARSED, SOLVED};

typedef std::tr1::unordered_map<int, int> atommap;

class Remapper{
protected:
	int 			maxnumber;

public:
	Remapper(): maxnumber(0){}

	virtual bool	hasVar		(const Atom& atom, Var& mappedvarifexists) const;
	virtual Var		getVar		(const Atom& atom);
	virtual Literal	getLiteral	(const Lit& lit);
	bool			wasInput	(int var)	const { return var<maxnumber; }
};

class SmartRemapper: public Remapper{
private:
	//Maps from NON-INDEXED to INDEXED atoms
	atommap 		origtocontiguousatommapper, contiguoustoorigatommapper;

public:
	bool	hasVar		(const Atom& atom, Var& mappedvarifexists) const;
	Var		getVar		(const Atom& atom);
	Literal	getLiteral	(const Lit& lit);

};

class WrapperPimpl{
private:
	bool 			optimization;
	SolverState 	state;

protected:
	SolverOption	_modes;

	std::vector<Monitor*> monitors;

public:
	Remapper*		remapper;

	Solution*		solutionmonitor; //Non-owning pointers

public:
	WrapperPimpl			(const SolverOption& modes);
	virtual ~WrapperPimpl();

	bool 	hasOptimization	() const { return optimization; }
	void 	solve			();

	virtual void 	addModel(const InnerModel& model); //virtual for MODSOLVER!
	void	notifyOptimalModelFound();

	int		getNbModelsFound() const { return solutionmonitor->getNbModelsFound(); }

	void	setSolutionMonitor	(Solution* sol);

	const SolverOption& modes()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }
	void 	printStatistics	() const;
	void 	printLiteral	(std::ostream& stream, const Lit& l) const;
	void 	printCurrentOptimum(const Weight& value) const;


	// MONITORING
	void	addMonitor(Monitor* const mon);
	template<class T>
	void 	notifyMonitor(const T& obj);

protected:
	bool 	finishParsing	();
	void	setOptimization	(bool opt) { optimization = opt; }

	virtual MinisatID::LogicSolver* getSolver() const = 0;

	Var 	checkAtom		(const Atom& atom);
	Lit 	checkLit		(const Literal& lit);
	void 	checkLits		(const std::vector<Literal>& lits, vec<Lit>& ll);
	void 	checkLits		(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms		(const std::vector<Atom>& atoms, std::vector<Var>& ll);
	void 	checkAtoms		(const std::map<Atom, Atom>& atoms, std::map<Var, Var>& ll);
	void 	checkLits		(const std::vector<std::vector<Literal> >& lits, vec<vec<Lit> >& ll);
	void 	checkLits		(const std::vector<std::vector<Literal> >& lits, std::vector<std::vector<Lit> >& ll);

	Remapper*		getRemapper		()	const { return remapper; }

	bool	canBackMapLiteral		(const Lit& lit) const;
	Literal getBackMappedLiteral	(const Lit& lit) const;
	std::vector<Literal> getBackMappedModel	(const vec<Lit>& model) const;

private:
	Solution& 	getSolMonitor() { return *solutionmonitor; }
	const Solution& getSolMonitor() const { return *solutionmonitor; }

	void	notifySmallestTseitin	(const Atom& tseitin);
};

template<>
void WrapperPimpl::notifyMonitor(const InnerPropagation& obj);

template<>
void WrapperPimpl::notifyMonitor(const InnerBacktrack& obj);

class PCWrapperPimpl: public MinisatID::WrapperPimpl{
private:
	MinisatID::PCSolver* solver;

public:
	PCWrapperPimpl		(const SolverOption& modes);
	virtual ~PCWrapperPimpl();

	template<class T>
	bool add(const T& formula);

protected:
	virtual MinisatID::PCSolver* getSolver() const { return solver; }
};

template<> bool PCWrapperPimpl::add(const Atom& sentence);
template<> bool PCWrapperPimpl::add(const Disjunction& sentence);
template<> bool PCWrapperPimpl::add(const DisjunctionRef& sentence);
template<> bool PCWrapperPimpl::add(const Equivalence& sentence);
template<> bool PCWrapperPimpl::add(const Rule& sentence);
template<> bool PCWrapperPimpl::add(const Set& sentence);
template<> bool PCWrapperPimpl::add(const WSet& sentence);
template<> bool PCWrapperPimpl::add(const WLSet& sentence);
template<> bool PCWrapperPimpl::add(const Aggregate& sentence);
template<> bool PCWrapperPimpl::add(const MinimizeSubset& sentence);
template<> bool PCWrapperPimpl::add(const MinimizeOrderedList& sentence);
template<> bool PCWrapperPimpl::add(const MinimizeVar& sentence);
template<> bool PCWrapperPimpl::add(const CPIntVarRange& sentence);
template<> bool PCWrapperPimpl::add(const CPIntVarEnum& sentence);
template<> bool PCWrapperPimpl::add(const CPBinaryRel& sentence);
template<> bool PCWrapperPimpl::add(const CPBinaryRelVar& sentence);
template<> bool PCWrapperPimpl::add(const CPSumWeighted& sentence);
template<> bool PCWrapperPimpl::add(const CPCount& sentence);
template<> bool PCWrapperPimpl::add(const CPAllDiff& sentence);
template<> bool PCWrapperPimpl::add(const ForcedChoices& sentence);
template<> bool PCWrapperPimpl::add(const SymmetryLiterals& sentence);
template<> bool PCWrapperPimpl::add(const Symmetry& sentence);

class SOWrapperPimpl: public MinisatID::WrapperPimpl{
private:
	MinisatID::SOSolver* solver;

public:
	SOWrapperPimpl		(const SolverOption& modes);
	virtual ~SOWrapperPimpl	();

	template<class T>
	bool add(int modalid, const T& formula);

protected:
	virtual MinisatID::SOSolver* getSolver() const { return solver; }
};

template<> bool SOWrapperPimpl::add(int modalid, const Atom& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const Disjunction& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const DisjunctionRef& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const Rule& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const Set& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const WSet& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const WLSet& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const Aggregate& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const RigidAtoms& sentence);
template<> bool SOWrapperPimpl::add(int modalid, const SubTheory& sentence);

}

#endif /* INTERFACEIMPL_HPP_ */
