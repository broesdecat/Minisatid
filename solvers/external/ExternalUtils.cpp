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

#include <cstdlib>
#include <stdio.h>

#include "solvers/external/ExternalUtils.hpp"

template <typename T>
string printWeight(const T& w){
	return "";
}

#ifdef GMPWEIGHT
	template <>
	string printWeight<mpz_class>(const mpz_class& w){
		return w.get_str();
	}
#else
	#ifdef BIGINTWEIGHT
		template <>
		string printWeight<BigInteger>(const BigInteger& w){
			return bigIntegerToString(w);
		}
	#else //INT_WEIGHT
		template <>
		string printWeight<int>(const int& w){
			char s[15];
			sprintf(s, "%d", w);
			return s;
		}
	#endif
#endif
