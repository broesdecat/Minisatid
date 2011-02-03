//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#ifndef SOLVERI_H_
#define SOLVERI_H_

#include <cstdio>

#include "utils/Utils.hpp"

namespace MinisatID {

class Solution;
class WLSImpl;

class LogicSolver{
private:
	SolverOption _modes;
	MinisatID::WLSImpl* _parent;
public:
	LogicSolver(MinisatID::SolverOption modes, MinisatID::WLSImpl* inter)
			:_modes(modes), _parent(inter){};
	virtual ~LogicSolver(){};

	virtual bool 	simplify() = 0;
	virtual void 	finishParsing	(bool& present, bool& unsat) = 0;

	virtual bool	solve(const vec<Lit>& assumptions, Solution* sol) = 0;

			int 	verbosity		() const	{ return modes().verbosity; }
	const SolverOption& modes		() const	{ return _modes; }

	MinisatID::WLSImpl* getParent	() const { return _parent; }

	virtual void 	printStatistics	() const = 0;
};

}

#endif /* SOLVERI_H_ */