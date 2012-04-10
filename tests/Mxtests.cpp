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
		options.verbosity = 10;
		auto space = new Space(options);
		extAdd(*space, Disjunction({mkPosLit(1),mkPosLit(2),mkPosLit(3)}));
		ModelExpandOptions mxopts(0, Models::ALL, Models::ALL);
		auto mx = ModelExpand(space, mxopts, {mkNegLit(2)});
		mx.execute();
		ASSERT_EQ(mx.getSolutions().size(), 3);
		auto mx2 = ModelExpand(space, mxopts, {mkNegLit(1)});
		mx2.execute();
		ASSERT_EQ(mx2.getSolutions().size(), 3);
		auto mx3 = ModelExpand(space, mxopts, {});
		mx3.execute();
		ASSERT_EQ(mx3.getSolutions().size(), 7);
	}

	// TODO lazy addition tests?

	// TODO prioritized optimization test

	vector<string> generateListOfMXFiles() {
		vector<string> testdirs {"ecnfinstances/"};
		return getAllFilesInDirs(getTestDirectory(), testdirs);
	}

	class MXFileTests: public ::testing::TestWithParam<string> {
	};
	TEST_P(MXFileTests, ECNF) {
		test(InputFormat::FODOT, GetParam());
	}

	INSTANTIATE_TEST_CASE_P(ModelExpansion, MXFileTests, ::testing::ValuesIn(generateListOfMXFiles()));
}
