/*
 * ExternalInterface.hpp
 *
 *  Created on: Jul 22, 2010
 *      Author: broes
 */

#ifndef EXTERNALINTERFACE_HPP_
#define EXTERNALINTERFACE_HPP_

#include "solvers/ExternalUtils.hpp"

#include <vector>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
using namespace std;

#include <tr1/unordered_map>
using namespace tr1;

#include "solvers/solverfwd.hpp"
#include "mtl/Vec.h"

#define reportf(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

//TODO here create the mapping of grounder integers to solving integers!
//Because grounder can leave (huge!) gaps which slow solving (certainly with arithmetic expressions).

class SolverInterface{
private:
	ECNF_mode _modes;

	int freeindex;
	unordered_map<int, int> origtocontiguousatommapper, contiguoustoorigatommapper;

	FILE* res;

public:
	SolverInterface(ECNF_mode modes):_modes(modes), freeindex(0), origtocontiguousatommapper(), contiguoustoorigatommapper(){};
	virtual ~SolverInterface(){};

	virtual void 	setNbModels(int nb) = 0;
			void	setRes(FILE* f){
		res = f;
	}

	virtual bool 	simplify() = 0;
	virtual bool 	solve() = 0;
	virtual bool 	finishParsing() = 0;

	int 			verbosity() const	{ return modes().verbosity; }
	const ECNF_mode& modes()	const	{ return _modes; }

protected:
	Var checkAtom(const Atom& atom);
	Lit checkLit(const Literal& lit);
	void checkLits(const vector<Literal>& lits, vec<Lit>& ll);
	void checkLits(const vector<Literal>& lits, vector<Lit>& ll);
	void checkAtoms(const vector<Atom>& lits, vector<Var>& ll);
	void checkLits(const vector<Literal>& lits, vector<Literal>& ll);

	bool	wasInput(int var) const { return freeindex>var; }
	Literal getOrigLiteral(const Lit& l) const;

	FILE* getRes() const { return res; }
};

class PCSolver;

class PropositionalSolver: public SolverInterface{
private:
	PCSolver* impl;
	PCSolver* getSolver() const { return impl; }

public:
	PropositionalSolver(ECNF_mode modes);
	~PropositionalSolver();

	void 	setNbModels		(int nb);

	bool 	simplify		();
	bool 	solve			();
	bool 	solve			(vector<vector<Literal> >& models);

	void	addVar			(Atom v);
	bool	addClause		(vector<Literal>& lits);
	bool	addRule			(bool conj, Literal head, vector<Literal>& lits);
	bool	addSet			(int id, vector<Literal>& lits);
	bool 	addSet			(int set_id, vector<LW>& lws);
	bool	addSet			(int id, vector<Literal>& lits, const vector<Weight>& w);
	bool	addAggrExpr		(Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined);
	bool	finishParsing	(); //throws UNSAT

    bool 	addMinimize		(const vector<Literal>& lits, bool subsetmnmz);
    bool 	addSumMinimize	(const Atom head, const int setid);

	bool 	addIntVar		(int groundname, int min, int max);
	bool 	addCPBinaryRel	(Literal head, int groundname, MINISAT::EqType rel, int bound);
	bool 	addCPSum		(Literal head, const vector<int>& termnames, MINISAT::EqType rel, int bound);
	bool 	addCPSum		(Literal head, const vector<int>& termnames, vector<int> mult, MINISAT::EqType rel, int bound);
	bool 	addCPSumVar		(Literal head, const vector<int>& termnames, MINISAT::EqType rel, int rhstermname);
	bool 	addCPSumVar		(Literal head, const vector<int>& termnames, vector<int> mult, MINISAT::EqType rel, int rhstermname);
	bool 	addCPCount		(const vector<int>& termnames, int value, MINISAT::EqType rel, int rhstermname);

	void 	printModel(const vector<Literal>& model) const;
};

typedef uint64_t modID;

class ModSolverData;

class ModalSolver: public SolverInterface{
private:
	ModSolverData* impl;
	ModSolverData* getSolver() const { return impl; }

public:
	ModalSolver				(ECNF_mode modes);
	virtual ~ModalSolver	();

	void	setNbModels		(int nb);

	bool 	simplify		();
	bool 	solve			();

	bool 	finishParsing	();

	//Add information for hierarchy
	bool 	addChild		(modID parent, modID child, Literal head);
	void	addAtoms		(modID modid, const vector<Atom>& atoms);

	//Add information for PC-Solver
	void 	addVar			(modID modid, Atom v);
	bool 	addClause		(modID modid, vector<Literal>& lits);
	bool 	addRule			(modID modid, bool conj, Literal head, vector<Literal>& lits);
	bool 	addSet			(modID modid, int set_id, vector<LW>& lws);
	bool 	addSet			(modID modid, int set_id, vector<Literal>& lits, vector<Weight>& w);
	bool 	addAggrExpr		(modID modid, Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined);
};

//Throw exceptions if the inputted literals are in the wrong format.
void checkLit(Literal lit);
void checkLits(const vector<Literal>& lits);

#endif /* EXTERNALINTERFACE_HPP_ */
