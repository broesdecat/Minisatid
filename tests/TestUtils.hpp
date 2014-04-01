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

int getExpectedNb(const std::string& instancefile);
bool needsSatCheck(const std::string& instancefile);
void runWithModelCheck(MinisatID::SolverOption options, const std::string& instancefile);

/**
 * NOTE: when findatmost is not 0, only so many models will be searched
 */
int runNoModelCheck(MinisatID::SolverOption options, const std::string& instancefile, int findatmost = 0);
}

#endif /* MINISATID_TESTS_UTILS_HPP_ */
