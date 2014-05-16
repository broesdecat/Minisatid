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

namespace MinisatID{

namespace Tests{
	struct SolverMOC: public LiteralPrinter{
	private: int start;
	public:
		SolverMOC():start(3){}
		std::vector<Disjunction*> disj;
		std::vector<Implication*> eqs;
		void createVar(Atom v, TheoryID){
			start = v+1;
		}
		int newAtom() { return start++; }
		bool add(const Disjunction& d){ disj.push_back(new Disjunction(d)); return true; }
		bool add(const Implication& eq){ eqs.push_back(new Implication(eq)); return true; }
		SATVAL isUnsat() const { return SATVAL::POS_SAT; }
		SATVAL satState() const { return SATVAL::POS_SAT; }
		lbool value(const Lit&) { return l_True; }
		lbool value(Atom) { return l_True; }
		lbool rootValue(const Lit&) const { return l_False; }
		Lit getTrueLit() const { return mkPosLit(1); }
		Lit getFalseLit() const { return mkPosLit(2); }
		int verbosity() const { return 1; }
		SolverMOC& getFactory(TheoryID) { return *const_cast<SolverMOC*>(this); }

		void setString(const Atom&, const std::string&){}

		TheoryID getTheoryID(){
			return TheoryID(1);
		}
	};

	void add(const Disjunction& d, SolverMOC& moc){
		moc.add(d);
	}

	void add(const Implication& d, SolverMOC& moc){
		moc.add(d);
	}

	TEST(SCCTest, Trivial) {
		SolverMOC moc;
		vector<toCNF::Rule*> rules;
		bool notunsat = MinisatID::toCNF::transformSCCtoCNF<SolverMOC>(moc, rules);
		EXPECT_TRUE(notunsat);
	}

	TEST(SCCTest, SimpleLoop) {
		SolverMOC moc;
		vector<toCNF::Rule*> rules;
		auto varone = moc.newAtom();
		auto vartwo = moc.newAtom();
		rules.push_back(new toCNF::Rule(false, varone, {mkPosLit(vartwo)}, {}));
		rules.push_back(new toCNF::Rule(false, vartwo, {mkPosLit(varone)}, {}));
		auto notunsat = MinisatID::toCNF::transformSCCtoCNF<SolverMOC>(moc, rules);
		EXPECT_TRUE(notunsat);
	}
}

}
