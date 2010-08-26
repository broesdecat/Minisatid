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

#ifndef ISOLVER_HPP_
#define ISOLVER_HPP_

#include "solvers/utils/Utils.hpp"

class PCSolver;

class SolverModule {
private:
	bool 			init;
	PCSolver* 		pcsolver; //NON-OWNING pointer

public:
	SolverModule(PCSolver* s): init(false), pcsolver(s){ }
	virtual ~SolverModule(){};

	bool isInitialized		()	const	{ return init; }
	void notifyInitialized	() 			{ assert(!init); init = true; }

	PCSolver* getPCSolver	()	const 	{ return pcsolver; }

	bool isTrue		(Lit l) const;
	bool isFalse	(Lit l) const;
	bool isUnknown	(Lit l) const;
	bool isTrue		(Var l) const;
	bool isFalse	(Var l) const;
	bool isUnknown	(Var l) const;

	int verbosity	() 		const;

	lbool		value(Var x) const;
	lbool		value(Lit p) const;
	int			nVars()      const;
};

#endif /* ISOLVER_HPP_ */
