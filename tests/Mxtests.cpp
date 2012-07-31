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

namespace Tests{
	TEST(MXTest, MultiAssumpSolve) {
		SolverOption options;
		options.verbosity = 0;
		auto space = new Space(options);
		extAdd(*space, Disjunction({mkPosLit(1),mkPosLit(2),mkPosLit(3)}));
		ModelExpandOptions mxopts(0, Models::NONE, Models::NONE);
		auto mx = ModelExpand(space, mxopts, {mkNegLit(2)});
		mx.execute();
		ASSERT_EQ(mx.getNbModelsFound(), 3);
		auto mx2 = ModelExpand(space, mxopts, {mkNegLit(1)});
		mx2.execute();
		ASSERT_EQ(mx2.getNbModelsFound(), 3);
		auto mx3 = ModelExpand(space, mxopts, {});
		mx3.execute();
		ASSERT_EQ(mx3.getNbModelsFound(), 7);
	}

	// TODO lazy addition tests?

	// TODO prioritized optimization test

	vector<string> generateListOfMXFiles() {
		vector<string> testdirs {
			"simple/",
			"agg/basic/",
			"agg/amn/",
			"agg/card/",
			"agg/eq/",
			"agg/max/",
			"agg/min/",
			"agg/prod/",
			"agg/sum/",
			"id/",
			"cp/",
			"cnf/"};
		return getAllFilesInDirs(getTestDirectory(), testdirs);
	}

	class MXFileTests: public ::testing::TestWithParam<string> {
	};
	TEST_P(MXFileTests, ECNF) {
		SolverOption options;
		options.inference = Inference::MODELEXPAND;
		options.nbmodels = 0;
		options.format = InputFormat::FODOT;
		options.verbosity = 0;
		runWithModelCheck(options, GetParam());
	}

	TEST_P(MXFileTests, ECNFFullWatches) {
		SolverOption options;
		options.inference = Inference::MODELEXPAND;
		options.nbmodels = 0;
		options.format = InputFormat::FODOT;
		options.verbosity = 0;
		options.watchesratio = 1;
		runWithModelCheck(options, GetParam());
	}

	TEST_P(MXFileTests, ECNFOptimalWatches) {
		SolverOption options;
		options.inference = Inference::MODELEXPAND;
		options.nbmodels = 0;
		options.format = InputFormat::FODOT;
		options.verbosity = 0;
		options.watchesratio = 0.76;
		runWithModelCheck(options, GetParam());
	}

	INSTANTIATE_TEST_CASE_P(ModelExpansion, MXFileTests, ::testing::ValuesIn(generateListOfMXFiles()));

	vector<string> generateListOfASPFiles() {
		vector<string> testdirs {};
		return getAllFilesInDirs(getTestDirectory(), testdirs);
	}

	class ASPFileTests: public ::testing::TestWithParam<string> {
	};
	TEST_P(ASPFileTests, ASP) {
		SolverOption options;
		options.inference = Inference::MODELEXPAND;
		options.nbmodels = 0;
		options.format = InputFormat::ASP;
		options.verbosity = 0;
		runWithModelCheck(options, GetParam());
	}

	INSTANTIATE_TEST_CASE_P(ModelExpansion, ASPFileTests, ::testing::ValuesIn(generateListOfASPFiles()));

	vector<string> generateListOfECNFErrorFiles() {
		vector<string> testdirs {"error/"};
		return getAllFilesInDirs(getTestDirectory(), testdirs);
	}

	class ECNFErrorFileTests: public ::testing::TestWithParam<string> {
	};
	TEST_P(ECNFErrorFileTests, ECNF) {
		SolverOption options;
		options.inference = Inference::MODELEXPAND;
		options.nbmodels = 0;
		options.format = InputFormat::FODOT;
		options.verbosity = 0;
		ASSERT_THROW(runNoModelCheck(options, GetParam()), idpexception);
	}

	INSTANTIATE_TEST_CASE_P(ModelExpansion, ECNFErrorFileTests, ::testing::ValuesIn(generateListOfECNFErrorFiles()));
}
