#include "AggTypes.h"
#include "cstdlib"

template <typename T>
string printWeight(const T& w){
	exit(1);
}

#ifdef GMP
template <>
string printWeight<mpz_class>(const mpz_class& w){
	return w.get_str();
}

#else
#ifdef BIGINT
template <>
string printWeight<BigInteger>(const BigInteger& w){
	return bigIntegerToString(w);
}

#else
template <>
string printWeight<int>(const int& w){
	char s[15];
	sprintf(s, "%d", w);
	return s;
}

#endif
#endif
