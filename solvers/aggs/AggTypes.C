#include "AggTypes.h"
#include "cstdlib"

template <typename T>
string printWeight(const T& w){
	exit(1);
}

#ifdef GMPWEIGHT
template <>
string printWeight<mpz_class>(const mpz_class& w){
	return w.get_str();
}
#endif
#ifdef BIGINTWEIGHT
template <>
string printWeight<BigInteger>(const BigInteger& w){
	return bigIntegerToString(w);
}
#endif
#ifdef INTWEIGHT
template <>
string printWeight<int>(const int& w){
	char s[15];
	sprintf(s, "%d", w);
	return s;
}
#endif
