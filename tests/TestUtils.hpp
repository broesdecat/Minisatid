/****************************************************************
 * Copyright 2010-2012 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat, Stef De Pooter, Johan Wittocx
 * and Bart Bogaerts, K.U.Leuven, Departement Computerwetenschappen,
 * Celestijnenlaan 200A, B-3001 Leuven, Belgium
 ****************************************************************/

#ifndef MINISATID_TESTS_UTILS_HPP_
#define MINISATID_TESTS_UTILS_HPP_
#include <string>

#include "gtest/gtest.h"
#include "external/Tasks.hpp"
#include "external/Space.hpp"
#include "external/utils/FileManagement.hpp"

namespace MinisatID {
std::string getTestDirectory();
}

namespace Tests {

void runWithModelCheck(MinisatID::InputFormat format, const std::string& instancefile);
int runNoModelCheck(MinisatID::InputFormat format, const std::string& instancefile);
}

#endif /* MINISATID_TESTS_UTILS_HPP_ */
