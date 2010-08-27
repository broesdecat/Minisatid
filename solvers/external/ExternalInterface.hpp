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

#include "solvers/external/ExternalUtils.hpp"

#include <map>
#include <vector>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
using namespace std;

#include <tr1/unordered_map>
using namespace tr1;

#include "solvers/SATUtils.h"
#include <tr1/memory>

#ifdef USEMINISAT22
using namespace Minisat;
#endif

#define reportf(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

//TODO here create the mapping of grounder integers to solving integers!
//Because grounder can leave (huge!) gaps which slow solving (certainly with arithmetic expressions).

//map is only a bit slower
typedef unordered_map<int, int> atommap;

class SolverInterface{
private:
	ECNF_mode _modes;

	//MAPS FROM NON-INDEXED TO INDEXED ATOMS!!!
	int maxnumber;
	atommap origtocontiguousatommapper, contiguoustoorigatommapper;

	FILE* res;

public:
	SolverInterface(ECNF_mode modes):
		_modes(modes), maxnumber(0),
		origtocontiguousatommapper(), contiguoustoorigatommapper(){};

	virtual ~SolverInterface(){};

	virtual void 	setNbModels		(int nb) = 0;
			void	setRes			(FILE* f)	{ res = f; }

	virtual bool 	simplify		() = 0;
	virtual bool 	solve			() = 0;
	virtual bool 	solve			(vector<vector<Literal> >& models) = 0;
	virtual bool 	finishParsing	() = 0;

	int 			verbosity		() const	{ return modes().verbosity; }
	const ECNF_mode& modes			()	const	{ return _modes; }

protected:
	Var checkAtom(const Atom& atom);
	Lit checkLit(const Literal& lit);
	void checkLits(const vector<Literal>& lits, vec<Lit>& ll);
	void checkLits(const vector<Literal>& lits, vector<Lit>& ll);
	void checkAtoms(const vector<Atom>& lits, vector<Var>& ll);
	//void checkLits(const vector<Literal>& lits, vector<Literal>& ll);

	bool	wasInput(int var) const { return var<maxnumber; }
	Atom 	getOrigAtom		(const Var& l) const;
	Literal getOrigLiteral	(const Lit& l) const;

	FILE* getRes() const { return res; }
};

template <class T>
class SolverInterface2: public SolverInterface{
private:
	T* solver;

public:
	SolverInterface2(ECNF_mode modes, T* solver):
		SolverInterface(modes),	solver(solver){};

	virtual ~SolverInterface2(){
		delete solver;
	};

	virtual void 	setNbModels(int nb) = 0;

	virtual bool 	simplify		() = 0;
			bool 	solve			();
			bool 	solve			(vector<vector<Literal> >& models);
	virtual bool 	finishParsing	() = 0;

	void 	printModel(const vector<Literal>& model) const;

protected:
	T* getSolver() const { return solver; }
};

class PCSolver;

class PropositionalSolver: public SolverInterface2<PCSolver>{

public:
	PropositionalSolver(ECNF_mode modes);
	~PropositionalSolver();

	void 	setNbModels		(int nb);

	bool 	simplify		();

	void	addVar			(Atom v);
	bool	addClause		(vector<Literal>& lits);
	bool	addRule			(bool conj, Literal head, const vector<Literal>& lits);
	bool	addSet			(int id, const vector<Literal>& lits);
	bool 	addSet			(int set_id, const vector<LW>& lws);
	bool	addSet			(int id, const vector<Literal>& lits, const vector<Weight>& w);
	bool	addAggrExpr		(Literal head, int setid, Weight bound, Bound sign, AggrType type, HdEq sem);
	bool	finishParsing	(); //throws UNSAT

    bool 	addMinimize		(const vector<Literal>& lits, bool subsetmnmz);
    bool 	addSumMinimize	(const Atom head, const int setid);

	bool 	addIntVar		(int groundname, int min, int max);
	bool 	addCPBinaryRel	(Literal head, int groundname, MINISAT::EqType rel, int bound);
	bool 	addCPBinaryRelVar	(Literal head, int groundname, MINISAT::EqType rel, int groundname2);
	bool 	addCPSum		(Literal head, const vector<int>& termnames, MINISAT::EqType rel, int bound);
	bool 	addCPSum		(Literal head, const vector<int>& termnames, vector<int> mult, MINISAT::EqType rel, int bound);
	bool 	addCPSumVar		(Literal head, const vector<int>& termnames, MINISAT::EqType rel, int rhstermname);
	bool 	addCPSumVar		(Literal head, const vector<int>& termnames, vector<int> mult, MINISAT::EqType rel, int rhstermname);
	bool 	addCPCount		(const vector<int>& termnames, int value, MINISAT::EqType rel, int rhstermname);
	bool 	addCPAlldifferent(const vector<int>& termnames);
};

typedef uint64_t modID;

class ModSolverData;

class ModalSolver: public SolverInterface2<ModSolverData>{

public:
	ModalSolver				(ECNF_mode modes);
	virtual ~ModalSolver	();

	void	setNbModels		(int nb);

	bool 	simplify		();

	bool 	finishParsing	();

	//Add information for hierarchy
	bool 	addChild		(modID parent, modID child, Literal head);
	bool	addAtoms		(modID modid, const vector<Atom>& atoms);

	//Add information for PC-Solver
	void 	addVar			(modID modid, Atom v);
	bool 	addClause		(modID modid, vector<Literal>& lits);
	bool 	addRule			(modID modid, bool conj, Literal head, vector<Literal>& lits);
	bool 	addSet			(modID modid, int set_id, vector<LW>& lws);
	bool 	addSet			(modID modid, int set_id, vector<Literal>& lits, vector<Weight>& w);
	bool 	addAggrExpr		(modID modid, Literal head, int setid, Weight bound, Bound sign, AggrType type, HdEq sem);
};

//Throw exceptions if the inputted literals are in the wrong format.
void checkLit(Literal lit);
void checkLits(const vector<Literal>& lits);

#endif /* EXTERNALINTERFACE_HPP_ */
