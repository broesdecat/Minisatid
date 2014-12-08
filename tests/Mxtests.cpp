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
#include "external/utils/ResourceManager.hpp"
#include "external/FlatZincRewriter.hpp"
#include "Run.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "space/SearchEngine.hpp"

using namespace std;
using namespace MinisatID;

namespace Tests {
// TODO enable fullmodelcheck for small enough tests

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

// NOTE: add / at end!
vector<string> generateListOfMXFiles() {
	vector<string> testdirs { "ecnf/simple/", "ecnf/agg/basic/", "ecnf/agg/amn/", "ecnf/agg/card/", "ecnf/agg/eq/", "ecnf/agg/max/",
		"ecnf/agg/min/", "ecnf/agg/prod/", "ecnf/agg/sum/", "ecnf/id/", "ecnf/cp/", "ecnf/cnf/",
		"ecnf/grounded/", "ecnf/qbf/"};
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
vector<string> generateListOfFZFiles() {
	vector<string> testdirs { "flatzinc/" };
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
class FZFileTests: public ::testing::TestWithParam<string> {
};
class OPBFileTests: public ::testing::TestWithParam<string> {
};
class ECNFErrorFileTests: public ::testing::TestWithParam<string> {
};

TEST_P(MXFileTests, ECNF) {
	auto options = createMXOptions(InputFormat::FODOT);
	runWithModelCheck(options, GetParam());
}

TEST_P(MXFileTests, ECNFPreprocessing) {
	auto options = createMXOptions(InputFormat::FODOT);
	options.usesimplifier = true;
	runWithModelCheck(options, GetParam());
}

TEST_P(MXFileTests, ECNFToCNF) {
//	auto options = createMXOptions(InputFormat::FODOT);
//	options.tocnf = true;
//	runWithModelCheck(options, GetParam());
}

// cOn hold until anyone continues to work on it (most errors because of unsupported definitions in flatzinc)
/*TEST_P(MXFileTests, ECNFtoFZtoSolve) {
	cerr <<"Running instance " <<GetParam() <<"\n";
	stringstream ss;
	if(needsSatCheck(GetParam())){
		ss <<"/tmp/SAToutput";
	}else{
		auto expectednbmodels = getExpectedNb(GetParam());
		ss <<"/tmp/" <<expectednbmodels <<"SAToutput";
	}
	auto options = createMXOptions(InputFormat::FODOT);
	auto resfile = createResMan(ss.str());
	ostream output(resfile->getBuffer());
	FlatZincRewriter<ostream> t(options, output);
	parseAndInitializeTheory(GetParam(), &t);
	t.execute();

	auto options2 = createMXOptions(InputFormat::FLATZINC);
	runWithModelCheck(options2, ss.str());
}*/

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
	auto options = createMXOptions(InputFormat::ASP);
	options.defsem = DEFSEM::DEF_STABLE;
	runWithModelCheck(options, GetParam());
}

TEST_P(FZFileTests, Flatzinc) {
	auto options = createMXOptions(InputFormat::FLATZINC);
	runWithModelCheck(options, GetParam());
}

TEST_P(OPBFileTests, OPB) {
	auto options = createMXOptions(InputFormat::OPB);
	//options.watchesratio = 0.76;
	runWithModelCheck(options, GetParam());
}

TEST_P(ECNFErrorFileTests, ECNF) {
	ASSERT_THROW(runNoModelCheck(createMXOptions(InputFormat::FODOT), GetParam()), idpexception);
}

INSTANTIATE_TEST_CASE_P(ModelExpansion, MXFileTests, ::testing::ValuesIn(generateListOfMXFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, ASPFileTests, ::testing::ValuesIn(generateListOfASPFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, FZFileTests, ::testing::ValuesIn(generateListOfFZFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, OPBFileTests, ::testing::ValuesIn(generateListOfOPBFiles()));
INSTANTIATE_TEST_CASE_P(ModelExpansion, ECNFErrorFileTests, ::testing::ValuesIn(generateListOfECNFErrorFiles()));
}
