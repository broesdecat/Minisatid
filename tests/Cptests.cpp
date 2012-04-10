/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "TestUtils.hpp"
#include "external/Constraints.hpp"
#include "theorysolvers/PCSolver.hpp"

using namespace std;
using namespace MinisatID;

namespace Tests{

TEST(CPTest, UnSatCPSum) {
	SolverOption options;
	auto space = new Space(options);
	extAdd(*space, Disjunction({mkPosLit(1), mkNegLit(2), mkPosLit(3)}));
	extAdd(*space, Disjunction({mkPosLit(1), mkPosLit(2), mkPosLit(3)}));
	extAdd(*space, Disjunction({mkNegLit(3)}));
	uint groundone=1, groundtwo=2;
	extAdd(*space, IntVarRange(groundone, -3, 7));
	extAdd(*space, IntVarRange(groundtwo, 7, 10));
	extAdd(*space, CPSumWeighted(1, {groundone, groundtwo}, {Weight(1),Weight(1)}, EqType::GEQ, Weight(18)));

	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, {});
	mx.execute();
	ASSERT_TRUE(mx.isUnsat());
	delete(space);
}

//Magic sequence problem
TEST(CPTest, MagicSeq) {
	SolverOption options;
	auto space = new Space(options);

	extAdd(*space, Disjunction({mkPosLit(1), mkPosLit(2), mkPosLit(3)}));
	vector<Weight> mult;
	vector<uint> elemx;
	int n = 100;
	for(int i=0; i<n; ++i){
		mult.push_back(Weight(i-1));
		int x = i;
		extAdd(*space, IntVarRange(x, 0, n));
		elemx.push_back(x);
	}

	vector<Weight> weights;
	weights.resize(elemx.size(),Weight(1));

	for(int i=0; i<n; ++i){
		extAdd(*space, CPCount(elemx, i, EqType::EQ, elemx[i]));
	}
	extAdd(*space, Disjunction({mkPosLit(4)}));
	extAdd(*space, CPSumWeighted(4, elemx, weights, EqType::EQ, n));

	extAdd(*space, Disjunction({mkPosLit(5)}));
	extAdd(*space, CPSumWeighted(5, elemx, mult, EqType::EQ, 0));

	int literalcount = 6;
	for(int i=0; i<n; ++i){
		for(int j=0; j<n; ++j){
			extAdd(*space, CPBinaryRel(literalcount++, elemx[i], EqType::EQ, Weight(j)));
			extAdd(*space, CPBinaryRel(literalcount++, elemx[i], EqType::GEQ, Weight(j)));
		}
	}

	ModelExpandOptions mxoptions(2, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, {});
	mx.execute();
	ASSERT_TRUE(mx.isUnsat());
	delete(space);
}

TEST(CPTest, Unsat2) {
	SolverOption options;
	auto space = new Space(options);

	vector<uint> elemx;
	uint n = 4;
	for(uint i=1; i<n; ++i){
		extAdd(*space, IntVarRange(i, 1, 2));
		elemx.push_back(i);
	}

	int c = 1;
	for(uint i=0; i<elemx.size(); ++i){
		int left = c;
		for(uint j=0; j<elemx.size(); ++j, ++c){
			extAdd(*space, CPBinaryRelVar(c, elemx[i], EqType::NEQ, elemx[j]));
			if(i+j<n){
				extAdd(*space, Disjunction({mkPosLit(left), mkPosLit(c+i+1)}));
			}
		}
	}

	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, {});
	mx.execute();
	ASSERT_TRUE(mx.isUnsat());
	delete(space);
}

}
