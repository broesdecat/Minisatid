/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include <cmath>

#include "TestUtils.hpp"
#include "external/Constraints.hpp"
#include "theorysolvers/PCSolver.hpp"

using namespace std;
using namespace MinisatID;

namespace Tests {
TEST(MXTest, MultiAssumpSolve) {
	SolverOption options;
	options.verbosity = 0;
	auto space = new Space(options);
	extAdd(*space, Disjunction( { mkPosLit(1), mkPosLit(2), mkPosLit(3) }));
	ModelExpandOptions mxopts(0, Models::NONE, Models::NONE);
	auto mx = ModelExpand(space, mxopts, { mkNegLit(2) });
	mx.execute();
	ASSERT_EQ(mx.getNbModelsFound(), 3);
	auto mx2 = ModelExpand(space, mxopts, { mkNegLit(1) });
	mx2.execute();
	ASSERT_EQ(mx2.getNbModelsFound(), 3);
	auto mx3 = ModelExpand(space, mxopts, { });
	mx3.execute();
	ASSERT_EQ(mx3.getNbModelsFound(), 7);
}

// TODO lazy addition tests?

// TODO prioritized optimization test

SolverOption createMXOptions(InputFormat format) {
	SolverOption options;
	options.inference = Inference::MODELEXPAND;
	options.nbmodels = 0;
	options.format = format;
	options.verbosity = 0;
	return options;
}

vector<string> generateListOfMXFiles() {
	vector<string> testdirs { "ecnf/simple/", "ecnf/agg/basic/", "ecnf/agg/amn/", "ecnf/agg/card/", "ecnf/agg/eq/", "ecnf/agg/max/",
		"ecnf/agg/min/", "ecnf/agg/prod/", "ecnf/agg/sum/", "ecnf/id/", "ecnf/cp/", "ecnf/cnf/" };
	return getAllFilesInDirs(getTestDirectory(), testdirs);
}
vector<string> generateListOfECNFErrorFiles() {
	vector<string> testdirs { "ecnf/error/" };
	return getAllFilesInDirs(getTestDirectory(), testdirs);
}
vector<string> generateListOfASPFiles() {
	vector<string> testdirs { "lparse/" };
	return getAllFilesInDirs(getTestDirectory(), testdirs);
}
vector<string> generateListOfOPBFiles() {
	vector<string> testdirs { "opb/" };
	return getAllFilesInDirs(getTestDirectory(), testdirs);
}

class MXFileTests: public ::testing::TestWithParam<string> {
};
class ASPFileTests: public ::testing::TestWithParam<string> {
};
class OPBFileTests: public ::testing::TestWithParam<string> {
};
class ECNFErrorFileTests: public ::testing::TestWithParam<string> {
};

TEST_P(MXFileTests, ECNF) {
	runWithModelCheck(createMXOptions(InputFormat::FODOT), GetParam());
}

TEST_P(MXFileTests, ECNFFullWatches) {
	auto options = createMXOptions(InputFormat::FODOT);
	options.watchesratio = 1;
	runWithModelCheck(options, GetParam());
}

TEST_P(MXFileTests, ECNFOptimalWatches) {
	auto options = createMXOptions(InputFormat::FODOT);
	options.watchesratio = 0.76;
	runWithModelCheck(options, GetParam());
}

TEST_P(ASPFileTests, ASP) {
	runWithModelCheck(createMXOptions(InputFormat::ASP), GetParam());
}

TEST_P(OPBFileTests, OPB) {
	runWithModelCheck(createMXOptions(InputFormat::OPB), GetParam());
}

TEST_P(ECNFErrorFileTests, ECNF) {
	ASSERT_THROW(runNoModelCheck(createMXOptions(InputFormat::FODOT), GetParam()), idpexception);
}

INSTANTIATE_TEST_CASE_P(ModelExpansion, MXFileTests, ::testing::ValuesIn(generateListOfMXFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, ASPFileTests, ::testing::ValuesIn(generateListOfASPFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, OPBFileTests, ::testing::ValuesIn(generateListOfOPBFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, ECNFErrorFileTests, ::testing::ValuesIn(generateListOfECNFErrorFiles()));
}
