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
#include "external/Translator.hpp"

#include "theorysolvers/LogicSolver.hpp"
//Have to be included, otherwise this header knows nothing of the inheritance between LogicSolver and its children
#include "theorysolvers/PCSolver.hpp"
#include "theorysolvers/SOSolver.hpp"

#ifndef __GXX_EXPERIMENTAL_CXX0X__
#include <tr1/memory>
#endif

namespace MinisatID {

class WrappedLogicSolver;
class WrappedSOSolver;
class WrappedPCSolver;
#ifdef __GXX_EXPERIMENTAL_CXX0X__
	typedef std::shared_ptr<WrappedLogicSolver> pwls;
	typedef std::shared_ptr<WrappedSOSolver> pwsos;
	typedef std::shared_ptr<WrappedPCSolver> pwps;
#else
	typedef std::tr1::shared_ptr<WrappedLogicSolver> pwls;
	typedef std::tr1::shared_ptr<WrappedSOSolver> pwsos;
	typedef std::tr1::shared_ptr<WrappedPCSolver> pwps;
#endif

typedef std::tr1::unordered_map<int, int> atommap;

class LogicSolver;
class PCSolver;
class SOSolver;

///////
// Generic model expansion solution datastructure
///////

class Solution{
private:
	const bool 	printmodels, savemodels, search;
	//bool 		nomoremodels;
	const int 	nbmodelstofind;
	int 		nbmodelsfound;
	std::vector<std::vector<Literal> > 	models;
	const std::vector<Literal> 			assumptions;

public:
	Solution(bool print, bool save, bool search, int searchnb, const std::vector<Literal>& assumpts):
			printmodels(print), savemodels(save), search(search),
			nbmodelstofind(searchnb), nbmodelsfound(0),
			assumptions(assumpts){}
	~Solution(){};

	void 		addModel		(std::vector<Literal> model) {
		nbmodelsfound++;
		if(getSave()){
			models.push_back(model);
		}
	}

	int 		getNbModelsFound		() 			{ return nbmodelsfound; }
	int 		getNbModelsToFind() const	{ return nbmodelstofind; }
	bool 		getPrint		() const 	{ return printmodels; }
	bool 		getSave			() const 	{ return savemodels; }
	bool 		getSearch		() const 	{ return search; }

	const std::vector<Literal>& 				getAssumptions	() { return assumptions; }

	/**
	 * IMPORTANT: only allowed when the models are being saved!
	 */
	const std::vector<std::vector<Literal> >& 	getModels		() {
		if(!savemodels) throw idpexception("Models were not being saved!\n");
		return models;
	}
};

///////
// External interfaces offered from the solvers
///////

class WrappedLogicSolver{
private:
	SolverOption	_modes;

	//Maps from NON-INDEXED to INDEXED atoms!
	int 		maxnumber;
	atommap 	origtocontiguousatommapper, contiguoustoorigatommapper;

	Translator* _translator;

	bool 		firstmodel; //True if the first model has not yet been printed

public:
	WrappedLogicSolver(const SolverOption& modes);
	virtual ~WrappedLogicSolver(){
		delete _translator;
	};

	virtual void 	printStatistics	() const = 0;

	virtual bool 	simplify		();
	virtual bool 	solve			(Solution* sol);
			void 	addModel		(const vec<Lit>& model, Solution* sol);
	virtual bool 	finishParsing	();

	int 			verbosity		() const	{ return modes().verbosity; }
	const SolverOption& modes		() const	{ return _modes; }
	void			setNbModels		(int nb) 	{ _modes.nbmodels = nb; }
	bool			hasTranslator	() const { return _translator!=NULL; }
	Translator*		getTranslator	() const { return _translator; }
	void			setTranslator	(Translator* translator) { _translator = translator; }

	int				getMaxNumberUsed()	const { return maxnumber; }
	Literal 		getOrigLiteral	(const Lit& l) const;

protected:
	virtual MinisatID::LogicSolver* getSolver() const = 0;

	Var 	checkAtom	(const Atom& atom);
	Lit 	checkLit	(const Literal& lit);
	void 	checkLits	(const std::vector<Literal>& lits, vec<Lit>& ll);
	void 	checkLits	(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms	(const std::vector<Atom>& lits, std::vector<Var>& ll);

	bool	wasInput(int var) const { return var<maxnumber; }
	Atom 	getOrigAtom		(const Var& l) const;

	std::streambuf* 	getRes() const;
};

class WrappedPCSolver: public MinisatID::WrappedLogicSolver{
private:
	MinisatID::PCSolver* solver;

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

	void 	printStatistics	() const;

protected:
	virtual MinisatID::PCSolver* getSolver() const;
};

class WrappedSOSolver: public MinisatID::WrappedLogicSolver{
private:
	MinisatID::SOSolver* solver;

public:
	WrappedSOSolver				(const SolverOption& modes);
	virtual ~WrappedSOSolver	();

	//Add information for hierarchy
	bool 	addChild		(vsize parent, vsize child, Literal head);
	bool	addAtoms		(vsize modid, const std::vector<Atom>& atoms);

	//Add information for PC-Solver
	//void 	addVar			(vsize modid, Atom v);
	bool 	addClause		(vsize modid, std::vector<Literal>& lits);
	bool 	addRule			(vsize modid, bool conj, Literal head, std::vector<Literal>& lits);
	bool 	addSet			(vsize modid, int set_id, std::vector<WLtuple>& lws);
	bool 	addSet			(vsize modid, int set_id, std::vector<Literal>& lits, std::vector<Weight>& w);
	bool 	addAggrExpr	(vsize modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem);

	void 	printStatistics	() const { report("Statistics printing not implemented for modal solver.\n");}

protected:
	virtual MinisatID::SOSolver* getSolver() const;
};

}

#endif /* EXTERNALINTERFACE_HPP_ */
