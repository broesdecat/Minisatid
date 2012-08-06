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
void runWithModelCheck(SolverOption options, const string& instancefile) {
	auto dirlist = split(instancefile, "/");
	auto list = split(dirlist.back(), "SAT");
	ASSERT_EQ((uint)2, list.size());
	auto expectednbmodels = 0;
	auto prefix = list.front();
	bool satcheck = false;
	if(prefix.size()==2 && tolower(prefix[0])=='u' && tolower(prefix[1])=='n'){
		expectednbmodels = 0;
	}else{
		if(list.front().size()==0){
			satcheck = true;
			expectednbmodels = 1;
		}else{
			expectednbmodels = atoi(list.front().c_str());
		}
	}

//	cerr <<"Expecting " <<(satcheck?"at least ":"exactly ") <<expectednbmodels <<" models.\n";
	auto modelsfound = runNoModelCheck(options, instancefile, expectednbmodels+1);
//	cerr <<"Found " <<modelsfound <<" models.\n";
	if(satcheck){
		ASSERT_LT(0, modelsfound);
	}else{
		ASSERT_EQ(expectednbmodels, modelsfound);
	}
}

int runNoModelCheck(SolverOption options, const std::string& instancefile, int findatmost) {
	cerr <<"Running instance " <<instancefile <<"\n";
	options.nbmodels = findatmost;
	Space s(options);
	parseAndInitializeTheory(instancefile, &s);

	ModelExpandOptions mxoptions(0, Models::NONE, Models::NONE);
	mxoptions.nbmodelstofind = s.getOptions().nbmodels;

	auto mx = ModelExpand(&s, mxoptions, { });
	mx.execute();
	return mx.getNbModelsFound();
}
}
