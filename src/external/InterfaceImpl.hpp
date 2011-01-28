#ifndef INTERFACEIMPL_HPP_
#define INTERFACEIMPL_HPP_

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <tr1/unordered_map>

#include "external/ExternalUtils.hpp"

#include "theorysolvers/LogicSolver.hpp"
//Have to be included, otherwise this header knows nothing of the inheritance between LogicSolver and its children
#include "theorysolvers/PCSolver.hpp"
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
	int 	maxnumber;

public:
	Remapper(): maxnumber(0){}

	virtual Var		getVar		(const Atom& atom);
	//virtual Atom	getAtom		(const Var& var);
	//virtual Lit	getLit		(const Literal& literal);
	virtual Literal	getLiteral	(const Lit& lit);
	bool			wasInput(int var)	const { return var<maxnumber; }
};

class SmartRemapper: public Remapper{
private:
	//Maps from NON-INDEXED to INDEXED atoms!
	atommap 	origtocontiguousatommapper, contiguoustoorigatommapper;

public:
	Var		getVar		(const Atom& atom);
	//Atom	getAtom		(const Var& var);
	//Lit	getLit		(const Literal& literal);
	Literal	getLiteral	(const Lit& lit);

};

class WLSImpl{
private:
	SolverState 	_state;
	SolverOption	_modes;

	Remapper*		_remapper;
	Translator*		_translator;

	bool 		firstmodel; //True if the first model has not yet been printed

public:
	WLSImpl				(const SolverOption& modes);
	virtual ~WLSImpl	();

	void 	printStatistics	() const;

	bool 	finishParsing	();
	bool 	simplify		();
	bool 	solve			(Solution* sol);

	void 	printModel		(const vec<Lit>& model);
	void 	addModel		(const vec<Lit>& model, Solution* sol);

	const SolverOption& modes		()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }

	void	setTranslator	(Translator* translator);
	void 	printLiteral	(std::ostream& stream, const Lit& l) const;

protected:
	virtual MinisatID::LogicSolver* getSolver() const = 0;

	Var 	checkAtom	(const Atom& atom);
	Lit 	checkLit	(const Literal& lit);
	void 	checkLits	(const std::vector<Literal>& lits, vec<Lit>& ll);
	void 	checkLits	(const std::vector<Literal>& lits, std::vector<Lit>& ll);
	void 	checkAtoms	(const std::vector<Atom>& atoms, std::vector<Var>& ll);

	std::streambuf* 	getRes() const;

	Remapper*	getRemapper		()	const { return _remapper; }
	Translator*	getTranslator	()	const { return _translator; }
};

class WPCLSImpl: public MinisatID::WLSImpl{
private:
	MinisatID::PCSolver* solver;

public:
	WPCLSImpl(const SolverOption& modes);
	~WPCLSImpl();

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
	virtual MinisatID::PCSolver* getSolver() const;
};

class WSOLSImpl: public MinisatID::WLSImpl{
private:
	MinisatID::SOSolver* solver;

public:
	WSOLSImpl			(const SolverOption& modes);
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
	virtual MinisatID::SOSolver* getSolver() const;
};

}

#endif /* INTERFACEIMPL_HPP_ */
