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
	options.verbosity = 0;
	auto space = new Space(options);
	extAdd(*space, Disjunction(DEFAULTCONSTRID,{mkPosLit(1), mkNegLit(2), mkPosLit(3)}));
	extAdd(*space, Disjunction(DEFAULTCONSTRID,{mkPosLit(1), mkPosLit(2), mkPosLit(3)}));
	extAdd(*space, Disjunction(DEFAULTCONSTRID,{mkNegLit(3)}));
	VarID groundone={1}, groundtwo={2};
	extAdd(*space, IntVarRange(DEFAULTCONSTRID,groundone, -3, 7));
	extAdd(*space, IntVarRange(DEFAULTCONSTRID,groundtwo, 7, 10));
	extAdd(*space, CPSumWeighted(DEFAULTCONSTRID,mkPosLit(1), {groundone, groundtwo}, {Weight(1),Weight(1)}, EqType::GEQ, Weight(18)));

	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, {});
	mx.execute();
	ASSERT_TRUE(mx.isUnsat());
	delete(space);
}

//Magic sequence problem
TEST(CPTest, DISABLED_MagicSeq) {
	SolverOption options;
	options.verbosity = 0;
	auto space = new Space(options);

	extAdd(*space, Disjunction(DEFAULTCONSTRID,{mkPosLit(1), mkPosLit(2), mkPosLit(3)}));
	vector<Weight> mult;
	vector<VarID> elemx;
	int n = 100;
	for(int i=0; i<n; ++i){
		mult.push_back(Weight(i-1));
		VarID x = {i};
		extAdd(*space, IntVarRange(DEFAULTCONSTRID,x, 0, n));
		elemx.push_back(x);
	}

	vector<Weight> weights;
	weights.resize(elemx.size(),Weight(1));

	for(int i=0; i<n; ++i){
		extAdd(*space, CPCount(DEFAULTCONSTRID,elemx, i, EqType::EQ, elemx[i]));
	}
	extAdd(*space, Disjunction(DEFAULTCONSTRID,{mkPosLit(4)}));
	extAdd(*space, CPSumWeighted(DEFAULTCONSTRID,mkPosLit(4), elemx, weights, EqType::EQ, n));

	extAdd(*space, Disjunction(DEFAULTCONSTRID,{mkPosLit(5)}));
	extAdd(*space, CPSumWeighted(DEFAULTCONSTRID,mkPosLit(5), elemx, mult, EqType::EQ, 0));

	int literalcount = 6;
	for(int i=0; i<n; ++i){
		for(int j=0; j<n; ++j){
			extAdd(*space, CPBinaryRel(DEFAULTCONSTRID,mkPosLit(literalcount++), elemx[i], EqType::EQ, Weight(j)));
			extAdd(*space, CPBinaryRel(DEFAULTCONSTRID,mkPosLit(literalcount++), elemx[i], EqType::GEQ, Weight(j)));
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
	options.verbosity = 0;
	auto space = new Space(options);

	vector<VarID> elemx;
	uint n = 4;
	for(uint i=1; i<n; ++i){
		VarID x = {i};
		extAdd(*space, IntVarRange(DEFAULTCONSTRID,x, 1, 3));
		elemx.push_back(x);
	}

	int c = 1;
	for(uint i=0; i<elemx.size(); ++i){
		for(uint j=0; j<elemx.size(); ++j, ++c){
			extAdd(*space, CPBinaryRelVar(DEFAULTCONSTRID,mkPosLit(c), elemx[i], EqType::NEQ, elemx[j]));
			extAdd(*space, Disjunction(DEFAULTCONSTRID, {mkPosLit(c)}));
		}
	}

	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxoptions, {});
	mx.execute();
	ASSERT_TRUE(mx.isUnsat());
	delete(space);
}

}
