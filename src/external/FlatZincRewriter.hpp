/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <set>
#include <sstream>
#include <cstdlib>
#include <cstdint>
#include <cstdio>
#include <vector>
#include <iostream>
#include <fstream>

#include "ExternalUtils.hpp"
#include "ConstraintAdditionInterface.hpp"
#include "Tasks.hpp"

namespace MinisatID {

// External interfaces offered from the solvers

enum class SolverState { PARSING, FINISHING};

typedef std::vector<Weight> weightlist;

enum OptimFZ { MNMZ_NONE, MNMZ_VAR, MNMZ_SUBSET, MNMZ_AGG };

enum CloseConstraint {CLOSE, OPEN};

struct BinRel{
	Lit head;
	std::string left, right;
	EqType rel;
};

template<typename Stream>
class FlatZincRewriter: public ExternalConstraintVisitor, public Task{
private:
	SolverState 		state;
	SolverOption		_modes;

	uint 				maxatomnumber, maxcpnumber;
	std::set<uint> 		atomsseen, negatomsseen;
	std::set<uint> 		litatomsseen, litnegatomsseen;
	std::set<VarID>		cpvarsseen;
	std::map<VarID, std::pair<Weight, Weight> > varbounds;

	std::stringstream 	definitions, constraints;
	std::map<int, WLSet>	sets; //index is setID

	bool hasoptim;
	std::vector<OptimizeVar> 			savedvar; // To be added AFTER initialization
	std::vector<MinimizeAgg>			savedagg; // To be added AFTER initialization

	std::vector<Aggregate> savedaggs;
	std::vector<BinRel> savedbinrels;
	std::vector<CPSumWeighted> savedcpsums;

	Stream& stream;

public:
	FlatZincRewriter(const SolverOption& modes, Stream& stream);
	FlatZincRewriter(Remapper* remapper, Translator *translator, const SolverOption& modes, Stream& stream);
	virtual ~FlatZincRewriter();

	const SolverOption& modes()	const	{ return _modes; }
	int 	verbosity		()	const	{ return modes().verbosity; }

	bool	isParsing		() const { return state==SolverState::PARSING; }
	bool	isFinishing		() const { return state==SolverState::FINISHING; }

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
	virtual void add(const Disjunction&);
	virtual void add(const Implication&);
	virtual void add(const Rule&);
	virtual void add(const WLSet&);
	virtual void add(const Aggregate&);
	virtual void add(const OptimizeVar&);
	virtual void add(const MinimizeAgg&);
	virtual void add(const IntVarEnum&);
	virtual void add(const IntVarRange&);
	virtual void add(const CPBinaryRel&);
	virtual void add(const CPBinaryRelVar&);
	virtual void add(const CPSumWeighted&);
	// TODO additional constraints
  
  void execute();

protected:
	std::ostream& getOutput();

	const WLSet& getSet(uint i) const;

	void addLits(const litlist& lits);

	void check(const Atom& Var);
	void check(const Lit& lit);
	void check(const std::vector<Lit>& lits);
	void checkOnlyPos(const std::vector<Lit>& lits);
	void check(const std::vector<std::vector<Lit> >& lits);

	Atom newAtom();
	VarID newCpVar(const Weight& min, const Weight& max);
	VarID newCpVar(const std::vector<Weight>& values);
	void newIntVar(const Lit& lit, bool defined, int defID);
	void addIntegerVar(VarID varID, const std::string& domainexpr, const Weight& min, const Weight& max);

	const Weight& getMin(VarID var);
	const Weight& getMax(VarID var);

	void printRel(const std::string& left, const std::string& right, const Lit& head, const std::string& constr);
	void addBinRel(const std::string& left, const std::string& right, const Lit& head, EqType rel);
	void printSum(const weightlist& weights, const std::string& vars, const Lit& head, std::string constr, std::string bound);
	void addSum(const weightlist& weights, const std::vector<VarID>& vars, const Lit& head, EqType rel, const Weight& bound);
	void addSum(const weightlist& weights, const std::string& vars, const Lit& head, EqType rel, const Weight& bound);
	void addVarSum(const weightlist& weights, const std::string& vars, const Lit& head, EqType rel, VarID rhsvar, const Weight& min, const Weight& max);
	void addVarSum(const weightlist& weights, const std::vector<VarID>& vars, const Lit& head, EqType rel, VarID bound);
	void addVarSum(const weightlist& weights, const litlist& lits, const Lit& head, EqType rel, VarID bound);
	void addProduct(const Aggregate& agg, const WLSet& set);
	void addSum(const Aggregate& agg, const WLSet& set);
	void addEquiv(const Implication& impl, CloseConstraint close);

	VarID addOptimization(bool& minimize);
};

}
