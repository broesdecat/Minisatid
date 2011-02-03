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

#ifndef PRINT_HPP_
#define PRINT_HPP_

#include "utils/Utils.hpp"
#include "utils/PrintMessage.hpp"

namespace Minisat{
	class Solver;
}

/**
 * Verbosity rules:
 * level 0: no output
 * level 1: statistics information
 * level 2: initialization information + ?
 * ... FIXME
 */

namespace MinisatID {

namespace Print {

int getPrintableVar(Var v);

template<class T>
void print(const T& lit, const lbool val);

template<class S>
void print(S * const s);

template<class C>
void print(const C& c);

template<class S>
void print(rClause c, S * const s);

template<class T>
void printStatistics(T obj, int v = 1000){
	if(v>=1){
		obj->printStatistics();
	}
}

}

}

#endif /* PRINT_HPP_ */
