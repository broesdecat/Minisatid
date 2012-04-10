/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include <cmath>

#include "gtest/gtest.h"

#include "modules/SCCtoCNF.hpp"

using namespace std;
using namespace MinisatID;

// FIXME something wrong with having to include this operator here (because externalinterface.cpp is not in the test sources, which it shouldnt)
SATVAL operator&= (SATVAL orig, SATVAL add){
	return (orig==SATVAL::UNSAT||add==SATVAL::UNSAT)? SATVAL::UNSAT: SATVAL::POS_SAT;
}

namespace MinisatID{

namespace Tests{
	struct SolverMOC{
	private: int start;
	public:
		SolverMOC(int start):start(start){}
		std::vector<Disjunction*> disj;
		std::vector<Implication*> eqs;
		int newVar() { return start++; }
		bool add(const Disjunction& d){ disj.push_back(new Disjunction(d)); return true; }
		bool add(const Implication& eq){ eqs.push_back(new Implication(eq)); return true; }
		SATVAL isUnsat() const { return SATVAL::POS_SAT; }
		SATVAL satState() const { return SATVAL::POS_SAT; }
		lbool value(const Lit&) { return l_True; }
		lbool value(Var) { return l_True; }
	};

	void add(const Disjunction& d, SolverMOC& moc){
		moc.add(d);
	}

	void add(const Implication& d, SolverMOC& moc){
		moc.add(d);
	}

	TEST(SCCTest, Trivial) {
		SolverMOC moc(1);
		vector<toCNF::Rule*> rules;
		bool notunsat = MinisatID::toCNF::transformSCCtoCNF<SolverMOC>(moc, rules);
		EXPECT_TRUE(notunsat);
	}

	TEST(SCCTest, SimpleLoop) {
		SolverMOC moc(3);
		vector<toCNF::Rule*> rules;
		rules.push_back(new toCNF::Rule(false, 1, {mkPosLit(2)}, {}));
		rules.push_back(new toCNF::Rule(false, 2, {mkPosLit(1)}, {}));
		auto notunsat = MinisatID::toCNF::transformSCCtoCNF<SolverMOC>(moc, rules);
		EXPECT_TRUE(notunsat);
	}
}

}
