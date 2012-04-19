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
#include <cstdlib>
#include <cstdint>
#include <cstdio>
#include <vector>
#include <iostream>
#include <fstream>

#include "external/ExternalUtils.hpp"
#include "ConstraintVisitor.hpp"

namespace MinisatID {

// External interfaces offered from the solvers

enum class SolverState { PARSING, FINISHING};

typedef std::vector<Weight> weightlist;

enum OptimFZ { MNMZ_NONE, MNMZ_VAR, MNMZ_LIST, MNMZ_SUBSET, MNMZ_AGG };

enum CloseConstraint {CLOSE, OPEN};

struct BinRel{
	Var head;
	std::string left, right;
	EqType rel;

	BinRel():head(Var(0)){}
};

template<typename Stream>
class FlatZincRewriter: public ConstraintAdditionMonitor<Stream>{
private:
	SolverState 		state;
	SolverOption		_modes;

	uint 				maxatomnumber, maxcpnumber;
	std::set<uint> 		atomsseen, negatomsseen;
	std::set<uint> 		litatomsseen, litnegatomsseen;
	std::set<uint> 		cpvarsseen;
	std::map<uint, std::pair<Weight, Weight> > varbounds;

	std::stringstream 	definitions, constraints;
	std::map<int, WLSet>	sets; //index is setID

	bool hasoptim;
	std::vector<MinimizeVar> 			savedvar; // To be added AFTER initialization
	std::vector<MinimizeAgg>			savedagg; // To be added AFTER initialization
	std::vector<MinimizeOrderedList> 	savedlistmnmz; // To be added AFTER initialization

	std::vector<Aggregate> savedaggs;
	std::vector<BinRel> savedbinrels;
	std::vector<CPSumWeighted> savedcpsums;

	Stream& stream;

public:
	FlatZincRewriter(LiteralPrinter* pcsolver, const SolverOption& modes, Stream& stream);
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
	virtual void visit(const Disjunction&);
	virtual void visit(const Implication&);
	virtual void visit(const Rule&);
	virtual void visit(const WLSet&);
	virtual void visit(const Aggregate&);
	virtual void visit(const MinimizeOrderedList&);
	virtual void visit(const MinimizeVar&);
	virtual void visit(const MinimizeAgg&);
	virtual void visit(const IntVarEnum&);
	virtual void visit(const IntVarRange&);
	virtual void visit(const CPBinaryRel&);
	virtual void visit(const CPBinaryRelVar&);
	virtual void visit(const CPSumWeighted&);
	// TODO additional constraints

	virtual void notifyStart() {}
	virtual void notifyEnd();

protected:
	std::ostream& getOutput();

	const WLSet& getSet(uint i) const;

	void add(const litlist& lits);

	void check(const Var& Var);
	void check(const Lit& lit);
	void check(const std::vector<Lit>& lits);
	void checkOnlyPos(const std::vector<Lit>& lits);
	void check(const std::vector<std::vector<Lit> >& lits);

	Var createAtom();
	uint createCpVar(const Weight& min, const Weight& max);
	uint createCpVar(const std::vector<Weight>& values);
	void createIntVar(const Lit& lit, bool defined, int defID);
	void addIntegerVar(uint varID, const std::string& domainexpr, const Weight& min, const Weight& max);

	const Weight& getMin(uint var);
	const Weight& getMax(uint var);

	void printRel(const std::string& left, const std::string& right, const Lit& head, const std::string& constr);
	void addBinRel(const std::string& left, const std::string& right, const Lit& head, EqType rel);
	void printSum(const weightlist& weights, const std::string& vars, Var head, std::string constr, std::string bound);
	void addSum(const weightlist& weights, const std::vector<uint>& vars, Var head, EqType rel, const Weight& bound);
	void addSum(const weightlist& weights, const std::string& vars, Var head, EqType rel, const Weight& bound);
	void addVarSum(const weightlist& weights, const std::string& vars, Var head, EqType rel, uint rhsvar, const Weight& min, const Weight& max);
	void addVarSum(const weightlist& weights, const std::vector<uint>& lits, Var head, EqType rel, uint bound);
	void addVarSum(const weightlist& weights, const litlist& lits, Var head, EqType rel, uint bound);
	void addProduct(const Aggregate& agg, const WLSet& set);
	void addSum(const Aggregate& agg, const WLSet& set);
	void addEquiv(const Implication& impl, CloseConstraint close);

	uint addOptimization();
};

}

#endif /* INTERFACEIMPL_HPP_ */
