//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

#ifndef UNITTESTS_HPP_
#define UNITTESTS_HPP_

#include "external/ExternalInterface.hpp"

#ifndef __GXX_EXPERIMENTAL_CXX0X__
#include <tr1/memory>
#endif

namespace MinisatID {

#ifdef __GXX_EXPERIMENTAL_CXX0X__
typedef std::shared_ptr<WrappedLogicSolver> pwls;
#else
typedef std::tr1::shared_ptr<WrappedLogicSolver> pwls;
#endif

pwls unittest(SolverOption& modes);
pwls unittest2(SolverOption& modes);
pwls unittest3(SolverOption& modes);

}

#endif /* UNITTESTS_HPP_ */
