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
#include "utils/FileManagement.hpp"

using namespace std;

namespace MinisatID {
std::string getTestDirectory() {
	return string(MINISATIDTESTDIR) + '/';
}
}

namespace Tests {
void test(MinisatID::InputFormat format, const string& instancefile) {
	//FIXME add running tests comparable to idp
	throw exception();
}
}
