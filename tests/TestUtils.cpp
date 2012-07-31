/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
 ****************************************************************/

#include "TestUtils.hpp"
#include "Run.hpp"
#include "external/Space.hpp"
#include "utils/StringUtils.hpp"

using namespace std;
using namespace MinisatID;

namespace MinisatID {
std::string getTestDirectory() {
	return string(MINISATIDTESTDIR) + '/';
}
}

namespace Tests {
void runWithModelCheck(MinisatID::InputFormat format, const string& instancefile) {
	auto dirlist = split(instancefile, "/");
	auto list = split(dirlist.back(), "SAT");
	ASSERT_EQ(list.size(), (uint)2);
	auto expectednbmodels = 0;
	auto prefix = list.front();
	if(prefix.size()==2 && tolower(prefix[0])=='u' && tolower(prefix[1])=='n'){
		expectednbmodels = 0;
	}else{
		ASSERT_TRUE(list.front().size()>0);
		expectednbmodels = atoi(list.front().c_str());
	}

	auto modelsfound = runNoModelCheck(format, instancefile);
	ASSERT_EQ(modelsfound, expectednbmodels);
}
int runNoModelCheck(MinisatID::InputFormat format, const std::string& instancefile) {
	SolverOption modes;
	modes.inference = Inference::MODELEXPAND;
	modes.nbmodels = 0;
	modes.format = format;
	modes.verbosity = 0;

	Space s(modes);
	parseAndInitializeTheory(instancefile, &s);

	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	mxoptions.nbmodelstofind = s.getOptions().nbmodels;

	auto mx = ModelExpand(&s, mxoptions, { });
	mx.execute();
	return mx.getNbModelsFound();
}
}
