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
#include <unordered_map>

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
class SearchMonitor;
class InnerModel;
class LazyClauseMonitor;
class LazyClauseRef;

typedef std::vector<Lit> litlist;

// External interfaces offered from the solvers

enum SolverState { INIT, PARSED, SOLVED};

typedef std::unordered_map<int, int> atommap;

class Remapper{
protected:
	int maxnumber;

public:
	Remapper(): maxnumber(0){}
	virtual ~Remapper(){}

	virtual bool	hasVar		(const Atom& atom, Var& mappedvarifexists) const;
	virtual Var		getVar		(const Atom& atom);
	virtual Literal	getLiteral	(const Lit& lit);
	virtual Var 	getNewVar	() { assert(false); return -1; }
	virtual bool	wasInput	(Var var)const { return var<maxnumber; }
	virtual Var		largestVar	() const { return maxnumber; }
};

class SmartRemapper: public Remapper{
private:
	//Maps from NON-INDEXED to INDEXED atoms
	atommap 		origtocontiguousatommapper, contiguoustoorigatommapper;

public:
	bool	hasVar		(const Atom& atom, Var& mappedvarifexists) const;
	Var		getVar		(const Atom& atom);
	Literal	getLiteral	(const Lit& lit);
	Var 	getNewVar	();
	bool	wasInput	(Var var) const;
};

class WrapperPimpl{
private:
	bool 			optimization;
	SolverState 	state;

protected:
	SolverOption	_modes;

	std::vector<SearchMonitor*> monitors;

public:
	Remapper*		remapper;
	bool 			sharedremapper;

	Solution*		solutionmonitor; //Non-owning pointers

public:
	WrapperPimpl			(const SolverOption& modes);
	WrapperPimpl			(const SolverOption& modes, Remapper* sharedremapper);
	virtual ~WrapperPimpl();

	Var 	getNewVar();

	bool 	hasOptimization	() const { return optimization; }
	void 	solve			();
	void 	printTheory		(std::ostream& stream);

	virtual void 	addModel(const InnerModel& model); //virtual for MODSOLVER!
	void	notifyOptimalModelFound();

	int		getNbModelsFound() const { return solutionmonitor->getNbModelsFound(); }

	void	setSolutionMonitor	(Solution* sol);

	const SolverOption& modes()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }
	void 	printStatistics	() const;
	void 	printLiteral	(std::ostream& stream, const Lit& l) const;
	template<class List>
	void 	printTranslation(std::ostream& output, const List& l){
		std::vector<std::pair<uint, Literal>> litstoprint;
		for(auto i=l.cbegin(); i!=l.cend(); ++i){
			if(canBackMapLiteral(mkPosLit(*i))){
				// TODO NOTE: the theory is printed in the NEW vocabulary, not in the input one
				// So we print the new variable and the translation of its original version
				litstoprint.push_back(std::pair<uint, Literal>(*i, getRemapper()->getLiteral(mkPosLit(*i))));
			}
		}
		getSolMonitor().printTranslation(output, litstoprint);
	}
	void 	printCurrentOptimum(const Weight& value) const;

	Remapper* getRemapper		()	const { return remapper; }

	// MONITORING
	void	addMonitor(SearchMonitor* const mon);
	template<class T>
	void 	notifyMonitor(const T& obj);

protected:
	SATVAL 	finishParsing	();
	void	setOptimization	(bool opt) { optimization = opt; }

	virtual MinisatID::LogicSolver* getSolver() const = 0;

	Var 	checkAtom		(const Atom& atom);
	Lit 	checkLit		(const Literal& lit);
	void 	checkLits		(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms		(const std::vector<Atom>& atoms, std::vector<Var>& ll);
	void 	checkAtoms		(const std::map<Atom, Atom>& atoms, std::map<Var, Var>& ll);
	void 	checkLits		(const std::vector<std::vector<Literal> >& lits, std::vector<std::vector<Lit> >& ll);

	bool	canBackMapLiteral		(const Lit& lit) const;
	Literal getBackMappedLiteral	(const Lit& lit) const;
	std::vector<Literal> getBackMappedModel	(const std::vector<Lit>& model) const;

private:
	Solution& 	getSolMonitor() { return *solutionmonitor; }
	bool		hasSolMonitor() const { return solutionmonitor!=NULL; }
	const Solution& getSolMonitor() const { return *solutionmonitor; }

	void dontDecideTseitins(){
		Var i = 0;
		while(i<=getRemapper()->largestVar()){
			Var mappedvar;
			if(getRemapper()->hasVar(Atom(i), mappedvar)){
				getSolver()->notifyNonDecisionVar(mappedvar);
			}
			i++;
		}
	}
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
	SATVAL add(const T& formula);

protected:
	virtual MinisatID::PCSolver* getSolver() const { return solver; }
};

template<> SATVAL PCWrapperPimpl::add(const Atom& sentence);
template<> SATVAL PCWrapperPimpl::add(const Disjunction& sentence);
template<> SATVAL PCWrapperPimpl::add(const DisjunctionRef& sentence);
template<> SATVAL PCWrapperPimpl::add(const Equivalence& sentence);
template<> SATVAL PCWrapperPimpl::add(const Rule& sentence);
template<> SATVAL PCWrapperPimpl::add(const Set& sentence);
template<> SATVAL PCWrapperPimpl::add(const WSet& sentence);
template<> SATVAL PCWrapperPimpl::add(const WLSet& sentence);
template<> SATVAL PCWrapperPimpl::add(const Aggregate& sentence);
template<> SATVAL PCWrapperPimpl::add(const MinimizeSubset& sentence);
template<> SATVAL PCWrapperPimpl::add(const MinimizeOrderedList& sentence);
template<> SATVAL PCWrapperPimpl::add(const MinimizeVar& sentence);
template<> SATVAL PCWrapperPimpl::add(const MinimizeAgg& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPIntVarRange& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPIntVarEnum& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPBinaryRel& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPBinaryRelVar& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPSumWeighted& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPCount& sentence);
template<> SATVAL PCWrapperPimpl::add(const CPAllDiff& sentence);
template<> SATVAL PCWrapperPimpl::add(const ForcedChoices& sentence);
template<> SATVAL PCWrapperPimpl::add(const SymmetryLiterals& sentence);
template<> SATVAL PCWrapperPimpl::add(const Symmetry& sentence);
template<> SATVAL PCWrapperPimpl::add(const LazyGroundLit& sentence);

class SOWrapperPimpl: public MinisatID::WrapperPimpl{
private:
	MinisatID::SOSolver* solver;

public:
	SOWrapperPimpl		(const SolverOption& modes);
	virtual ~SOWrapperPimpl	();

	template<class T>
	SATVAL add(int modalid, const T& formula);

protected:
	virtual MinisatID::SOSolver* getSolver() const { return solver; }
};

template<> SATVAL SOWrapperPimpl::add(int modalid, const Atom& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const Disjunction& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const DisjunctionRef& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const Rule& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const Set& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const WSet& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const WLSet& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const Aggregate& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const RigidAtoms& sentence);
template<> SATVAL SOWrapperPimpl::add(int modalid, const SubTheory& sentence);

}

#endif /* INTERFACEIMPL_HPP_ */
