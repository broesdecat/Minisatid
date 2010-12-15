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

#include "satsolver/SATUtils.hpp"

using namespace MinisatID;

#ifdef USEMINISAT
rClause MinisatID::nullPtrClause = NULL;

pClause MinisatID::getClauseRef(rClause rc){
	return *rc;
}

Lit MinisatID::mkLit(Var x, bool sign){
	return Lit(x, sign);
}

double MinisatID::getDefaultDecay(){
	return 1/0.95;
}
double MinisatID::getDefaultRandfreq(){
	return 0.02;
}
POLARITY MinisatID::getDefaultPolarity(){
	return POL_STORED;
}
#endif

#ifdef USEMINISAT09Z
rClause MinisatID::nullPtrClause =  NULL;

pClause MinisatID::getClauseRef(rClause rc){
	return *rc;
}

Lit MinisatID::mkLit(Var x, bool sign){
	return Lit(x, sign);
}

double MinisatID::getDefaultDecay(){
	return 1/0.95;
}
double MinisatID::getDefaultRandfreq(){
	return 0.02;
}
POLARITY MinisatID::getDefaultPolarity(){
	return POL_STORED;
}
#endif

#ifdef USEMINISAT22
rClause MinisatID::nullPtrClause = Minisat::CRef_Undef;

pClause MinisatID::getClauseRef(rClause rc){
	return rc;
}

double MinisatID::getDefaultDecay(){
	return 0.95;
}
double MinisatID::getDefaultRandfreq(){
	return 0;
}
#endif
