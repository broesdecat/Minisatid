/*
 * Unittests.hpp
 *
 *  Created on: Jul 28, 2010
 *      Author: broes
 */

#ifndef UNITTESTS_HPP_
#define UNITTESTS_HPP_

#include "solvers/ExternalInterface.hpp"

shared_ptr<SolverInterface> unittest(ECNF_mode& modes);
shared_ptr<SolverInterface> unittest2(ECNF_mode& modes);
shared_ptr<SolverInterface> unittest3(ECNF_mode& modes);

#endif /* UNITTESTS_HPP_ */
