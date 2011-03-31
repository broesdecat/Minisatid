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

#include "solvers/cpsolver/CPScript.hpp"

using namespace CP;

CPScript::CPScript(): Space(){

}

CPScript::CPScript(bool share, CPScript& s): Space(share, s){
	for(vboolv::iterator i=s.boolvars.begin(); i<s.boolvars.end(); i++){
		boolvars.push_back(BoolVar());
		boolvars.back().update(*this, share, *i);
	}

	for(vintv::iterator i=s.intvars.begin(); i<s.intvars.end(); i++){
		intvars.push_back(IntVar());
		intvars.back().update(*this, share, *i);
	}
}

CPScript* CPScript::copy(bool share){
	return new CPScript(share, *this);
}

intvarindex CPScript::addIntVar(int min, int max){
	intvars.push_back(IntVar(*this, min, max));
	return intvars.size()-1;
}

boolvarindex CPScript::addBoolVar(){
	boolvars.push_back(BoolVar(*this, 0, 1));
	return boolvars.size()-1;
}

void CPScript::addBranchers(){
	IntVarArgs x(intvars.size());
	for(vintv::size_type i=0; i<intvars.size(); i++){
		x[i]=intvars[i];
	}
	branch(*this, x, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MAX);
}

ostream& CP::operator <<(ostream& ostream, const CPScript& script){
	ostream <<"Space:" <<endl;
	/*for(vboolv::const_iterator i=script.getBoolVars().begin(); i<script.getBoolVars().end(); i++){
		ostream << *i <<" " <<endl;
	}*/

	int count = 0;
	for(vintv::const_iterator i=script.getIntVars().begin(); i<script.getIntVars().end(); i++){
		Int::IntView v(*i);
		std::cout << "var " <<count++ << "=" <<v <<"; ";
		if(count%10 == 0){
			ostream <<endl;
		}
	}
	ostream <<endl;
	return ostream;
}
