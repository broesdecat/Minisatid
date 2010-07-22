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

#define reportf(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

class SolverInterface{
private:
	ECNF_mode _modes;
public:
	SolverInterface(ECNF_mode modes):_modes(modes){};
	virtual ~SolverInterface(){};

	virtual void 	setNbModels(int nb) = 0;
	virtual void	setRes(FILE* f) = 0;

	virtual bool 	simplify() = 0;
	virtual bool 	solve() = 0;
	virtual bool 	finishParsing() = 0;

	int 			verbosity() const	{ return modes().verbosity; }
	const ECNF_mode& modes()	const	{ return _modes; }
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
	void 	setRes			(FILE* f);

	bool 	simplify		();
	bool 	solve			();

	Atom	newVar			();
	void	addVar			(Atom v);
	void	addVars			(const vector<Literal>& a);
	bool	addClause		(vector<Literal>& lits);
	bool	addRule			(bool conj, vector<Literal>& lits);
	bool	addSet			(int id, vector<Literal>& lits);
	bool	addSet			(int id, vector<Literal>& lits, const vector<Weight>& w);
	bool	addAggrExpr		(Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined);
	bool	finishParsing	(); //throws UNSAT

    bool 	addMinimize		(const vector<Literal>& lits, bool subsetmnmz);
    bool 	addSumMinimize	(const Atom head, const int setid);
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
	void	setRes			(FILE* f);

	bool 	simplify		();
	bool 	solve			();

	bool 	finishParsing	();

	//Add information for hierarchy
	bool 	addChild		(modID parent, modID child, Literal head);
	void	addAtoms		(modID modid, const vector<Atom>& atoms);

	//Add information for PC-Solver
	void 	addVar			(modID modid, Atom v);
	bool 	addClause		(modID modid, vector<Literal>& lits);
	bool 	addRule			(modID modid, bool conj, vector<Literal>& lits);
	bool 	addSet			(modID modid, int set_id, vector<Literal>& lits, vector<Weight>& w);
	bool 	addAggrExpr		(modID modid, Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined);
};

#endif /* EXTERNALINTERFACE_HPP_ */
