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
#include "utils/Utils.hpp"

using namespace std;
using namespace MinisatID;

namespace Tests{
	struct SolverMOC{
	private: int start;
	public:
		SolverMOC(int start):start(start){}
		std::vector<InnerDisjunction*> disj;
		std::vector<InnerEquivalence*> eqs;
		int newVar() { return start++; }
		bool add(const InnerDisjunction& d){ disj.push_back(new InnerDisjunction(d)); return true; }
		bool add(const InnerEquivalence& eq){ eqs.push_back(new InnerEquivalence(eq)); return true; }
		bool isUnsat() const { return false; }
	};



	TEST(SCCTest, Trivial) {
		SolverMOC moc(1);
		vector<toCNF::Rule*> rules;
		bool notunsat = MinisatID::toCNF::transformSCCtoCNF<SolverMOC>(moc, rules);
		EXPECT_TRUE(notunsat);
	}

	TEST(SCCTest, SimpleLoop) {
		SolverMOC moc(3);
		vector<toCNF::Rule*> rules;
		vector<Var> pdef, qdef;
		pdef.push_back(2);
		qdef.push_back(1);
		vector<Lit> popen, qopen;
		rules.push_back(new toCNF::Rule(false, 1, pdef, popen));
		rules.push_back(new toCNF::Rule(false, 2, qdef, qopen));
		bool notunsat = MinisatID::toCNF::transformSCCtoCNF<SolverMOC>(moc, rules);
		EXPECT_TRUE(notunsat);
	}
}
