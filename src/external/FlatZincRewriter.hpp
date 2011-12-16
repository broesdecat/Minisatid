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

#include <set>
#include <sstream>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "external/ExternalInterface.hpp"
#include "external/ExternalUtils.hpp"

namespace MinisatID {

// External interfaces offered from the solvers

enum SolverState { PARSING, FINISHING};

typedef std::vector<Weight> weightlist;

enum OptimFZ { MNMZ_NONE, MNMZ_VAR, MNMZ_LIST, MNMZ_SUBSET, MNMZ_AGG };

enum CloseConstraint {CLOSE, OPEN};

struct BinRel{
	Atom head;
	std::string left, right;
	EqType rel;

	BinRel():head(Atom(0)){}
};

class FlatZincRewriter{
private:
	SolverState 		state;
	SolverOption		_modes;

	uint 				maxatomnumber, maxcpnumber;
	std::set<uint> 		atomsseen, negatomsseen;
	std::set<uint> 		litatomsseen, litnegatomsseen;
	std::set<uint> 		cpvarsseen;
	std::map<uint, std::pair<Weight, Weight> > varbounds;

	std::stringstream 	definitions, constraints;
	std::vector<WSet>	sets; //index is setID

	OptimFZ				optim;
	MinimizeVar 		savedvar; // To be added AFTER initialization
	MinimizeAgg			savedagg; // To be added AFTER initialization
	MinimizeOrderedList savedlistmnmz; // To be added AFTER initialization
	MinimizeSubset 		savedsubsetmnmz; // To be added AFTER initialization

	std::vector<Aggregate> savedaggs;
	std::vector<BinRel> savedbinrels;
	std::vector<CPSumWeighted> savedcpsums;

public:
	FlatZincRewriter			(const SolverOption& modes);
	virtual ~FlatZincRewriter();

	const SolverOption& modes()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }

	bool	isParsing		() const { return state==PARSING; }
	bool	isFinishing		() const { return state==FINISHING; }

	/**
	 * Way it works:
	 * 2 phases:
	 * 		parsing phase
	 * 		finishing phase
	 * 	during parsing, add as many relations as possible (if they don't require introducing new elements)
	 * 			and add ALL original variables!
	 * 	during finishing, add all remaining relations which need new variables.
	 * 			For this, we need to be sure what the maximum numbers are!
	 */
	template<class T>
	SATVAL 	add				(const T& formula);

	void	finishParsing	();

protected:
	std::ostream& getOutput();

	const WSet& getSet(uint i) const;

	template<typename T>
	void 	check			(const T& obj);
	template<typename T>
	void 	checkOnlyPos	(const T& obj);

	Atom createAtom();
	uint createCpVar(const Weight& min, const Weight& max);
	uint createCpVar(const std::vector<Weight>& values);
	void createIntVar(const Literal& lit, bool defined, int defID);
	void addIntegerVar(uint varID, const std::string& domainexpr, const Weight& min, const Weight& max);

	const Weight& getMin(uint var);
	const Weight& getMax(uint var);

	void add(const WSet& set, int setID);

	void printRel(const std::string& left, const std::string& right, const Literal& head, const std::string& constr);
	void addBinRel(const std::string& left, const std::string& right, const Literal& head, EqType rel);
	void printSum(const weightlist& weights, const std::string& vars, const Atom& head, std::string constr, std::string bound);
	void addSum(const weightlist& weights, const std::vector<uint>& vars, const Atom& head, EqType rel, const Weight& bound);
	void addSum(const weightlist& weights, const std::string& vars, const Atom& head, EqType rel, const Weight& bound);
	void addVarSum(const weightlist& weights, const std::string& vars, const Atom& head, EqType rel, uint rhsvar, const Weight& min, const Weight& max);
	void addVarSum(const weightlist& weights, const std::vector<uint>& lits, const Atom& head, EqType rel, uint bound);
	void addVarSum(const weightlist& weights, const std::vector<Literal>& lits, const Atom& head, EqType rel, uint bound);
	void addProduct(const Aggregate& agg, const WSet& set);
	void addSum(const Aggregate& agg, const WSet& set);
	void addEquiv(const Literal& head, const literallist& body, bool conjunctive, CloseConstraint close);

	uint addOptimization();
};

template<> void FlatZincRewriter::check(const Atom& atom);
template<> void FlatZincRewriter::check(const Literal& lit);
template<> void FlatZincRewriter::check(const std::vector<Literal>& lits);
template<> void FlatZincRewriter::checkOnlyPos(const std::vector<Literal>& lits);
template<> void FlatZincRewriter::check(const std::vector<std::vector<Literal> >& lits);
template<> void FlatZincRewriter::check(const std::vector<Atom>& atoms);

template<> SATVAL FlatZincRewriter::add(const literallist& lits);
template<> SATVAL FlatZincRewriter::add(const Disjunction& sentence);
template<> SATVAL FlatZincRewriter::add(const DisjunctionRef& sentence);
template<> SATVAL FlatZincRewriter::add(const Rule& sentence);
template<> SATVAL FlatZincRewriter::add(const Equivalence& sentence);
template<> SATVAL FlatZincRewriter::add(const Set& sentence);
template<> SATVAL FlatZincRewriter::add(const WSet& sentence);
template<> SATVAL FlatZincRewriter::add(const WLSet& sentence);
template<> SATVAL FlatZincRewriter::add(const Aggregate& sentence);
template<> SATVAL FlatZincRewriter::add(const MinimizeSubset& sentence);
template<> SATVAL FlatZincRewriter::add(const MinimizeOrderedList& sentence);
template<> SATVAL FlatZincRewriter::add(const MinimizeVar& sentence);
template<> SATVAL FlatZincRewriter::add(const MinimizeAgg& sentence);
template<> SATVAL FlatZincRewriter::add(const CPIntVarRange& sentence);
template<> SATVAL FlatZincRewriter::add(const CPIntVarEnum& sentence);
template<> SATVAL FlatZincRewriter::add(const CPBinaryRel& sentence);
template<> SATVAL FlatZincRewriter::add(const CPBinaryRelVar& sentence);
template<> SATVAL FlatZincRewriter::add(const CPSumWeighted& sentence);
template<> SATVAL FlatZincRewriter::add(const CPCount& sentence);
template<> SATVAL FlatZincRewriter::add(const CPAllDiff& sentence);

}

#endif /* INTERFACEIMPL_HPP_ */
