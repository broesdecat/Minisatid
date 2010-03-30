#include "AggTypes.h"

template <typename T>
string printWeight(const T& w){
	exit(1);
}

template <>
string printWeight<int>(const int& w){
	return "1";
}

template <>
string printWeight<BigInteger>(const BigInteger& w){
	return bigIntegerToString(w);
}
