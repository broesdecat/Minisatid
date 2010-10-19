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

#include "solvers/external/ExternalUtils.hpp"
#include "solvers/SolverI.hpp"
//Have to be included, otherwise this header knows nothing of the inheritance between Data and its children
#include "solvers/pcsolver/PCSolver.hpp"
#include "solvers/modsolver/SOSolverHier.hpp"

#include "solvers/SATUtils.h"

namespace MinisatID {

typedef std::tr1::unordered_map<int, int> atommap;

class Data;
class PCSolver;
class ModSolverData;

///////
// Generic model expansion solution datastructure
///////

class Solution{
private:
	const bool 	printmodels, savemodels;
	bool 		nomoremodels;
	const int 	nbmodelstofind;
	int 		nbmodelsfound;
	std::vector<std::vector<Literal> > 	models;
	const std::vector<Literal> 			assumptions;

public:
	Solution(bool print, bool save, int searchnb, const std::vector<Literal>& assumpts):
			printmodels(print), savemodels(save),
			nbmodelstofind(searchnb),
			assumptions(assumpts){}
	~Solution(){};

	void 		addModel		(std::vector<Literal> model) {
		nbmodelsfound++;
		if(getSave()){
			models.push_back(model);
		}
	}
	int 		modelCount		() { return nbmodelsfound; }

	int 		getNbModelsToFind() const { return nbmodelstofind; }
	bool 		getPrint		() const { return printmodels; }
	bool 		getSave			() const { return savemodels; }
	const std::vector<Literal>& 				getAssumptions	() { return assumptions; }
	const std::vector<std::vector<Literal> >& 	getModels		() {
		if(!savemodels) throw idpexception("Models were not being saved!\n");
		return models;
	}
};

class SolverInterface{
private:
	ECNF_mode _modes;

	//Maps from NON-INDEXED to INDEXED atoms!
	int 	maxnumber;
	atommap origtocontiguousatommapper, contiguoustoorigatommapper;

	FILE* 	res;

	Solution* 	currentsolution;
	bool 		firstmodel; //True if the first model has not yet been printed

public:
	SolverInterface(ECNF_mode modes);
	virtual ~SolverInterface(){};

			void	setRes			(FILE* f)	{ res = f; }

	virtual void 	printStatistics	() const = 0;
			void 	printModel		(const vec<Lit>& model);

	virtual bool 	simplify		();
	virtual void 	solve			(Solution* sol);
			void 	addModel		(const vec<Lit>& model);
	virtual bool 	finishParsing	();

	int 			verbosity		() const	{ return modes().verbosity; }
	const ECNF_mode& modes			() const	{ return _modes; }
	void			setNbModels		(int nb) 	{ _modes.nbmodels = nb; }

protected:
	virtual MinisatID::Data* getSolver() const = 0;

	Var 	checkAtom	(const Atom& atom);
	Lit 	checkLit	(const Literal& lit);
	void 	checkLits	(const std::vector<Literal>& lits, vec<Lit>& ll);
	void 	checkLits	(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms	(const std::vector<Atom>& lits, std::vector<Var>& ll);

	InternSol* mapToInternSol(Solution* sol);

	bool	wasInput(int var) const { return var<maxnumber; }
	Atom 	getOrigAtom		(const Var& l) const;
	Literal getOrigLiteral	(const Lit& l) const;

	FILE* 	getRes() const { return res; }
};

class PropositionalSolver: public MinisatID::SolverInterface{
private:
	MinisatID::PCSolver* solver;

public:
	PropositionalSolver(MinisatID::ECNF_mode modes);
	~PropositionalSolver();

	void	addVar			(Atom v);
	bool	addClause		(std::vector<Literal>& lits);
	bool	addRule			(bool conj, Literal head, const std::vector<Literal>& lits);
	bool	addSet			(int id, const std::vector<Literal>& lits);
	bool 	addSet			(int set_id, const std::vector<WLtuple>& lws);
	bool	addSet			(int id, const std::vector<Literal>& lits, const std::vector<Weight>& w);
	bool	addAggrExpr		(Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem);

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

class ModalSolver: public MinisatID::SolverInterface{
private:
	MinisatID::ModSolverData* solver;

public:
	ModalSolver				(MinisatID::ECNF_mode modes);
	virtual ~ModalSolver	();

	//Add information for hierarchy
	bool 	addChild		(vsize parent, vsize child, Literal head);
	bool	addAtoms		(vsize modid, const std::vector<Atom>& atoms);

	//Add information for PC-Solver
	void 	addVar			(vsize modid, Atom v);
	bool 	addClause		(vsize modid, std::vector<Literal>& lits);
	bool 	addRule			(vsize modid, bool conj, Literal head, std::vector<Literal>& lits);
	bool 	addSet			(vsize modid, int set_id, std::vector<WLtuple>& lws);
	bool 	addSet			(vsize modid, int set_id, std::vector<Literal>& lits, std::vector<Weight>& w);
	bool 	addAggrExpr		(vsize modid, Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem);

	void 	printStatistics	() const { reportf("Statistics printing not implemented for modal solver.\n");}

protected:
	virtual MinisatID::ModSolverData* getSolver() const;
};

}

#endif /* EXTERNALINTERFACE_HPP_ */
