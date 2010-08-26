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

#include "solvers/pcsolver/SolverModule.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

int SolverModule::verbosity() const	{
	return getPCSolver()->verbosity();
}

bool SolverModule::isTrue(Lit l) const {
	return value(l) == l_True;
}
bool SolverModule::isTrue(Var v) const {
	return value(v) == l_True;
}
bool SolverModule::isFalse(Lit l) const {
	return value(l) == l_False;
}
bool SolverModule::isFalse(Var v) const {
	return value(v) == l_False;
}
bool SolverModule::isUnknown(Lit l) const {
	return value(l) == l_Undef;
}
bool SolverModule::isUnknown(Var v) const {
	return value(v) == l_Undef;
}
lbool SolverModule::value(Var x) const {
	return getPCSolver()->value(x);
}
lbool SolverModule::value(Lit p) const {
	return getPCSolver()->value(p);
}
int SolverModule::nVars() const {
	return getPCSolver()->nVars();
}
