#include "AggTypes.h"

template <typename T>
const char* printWeight(T w){
	exit(1);
}

template <>
const char* printWeight<int>(int w){
	return "1";
}

template <>
const char* printWeight<BigInteger>(BigInteger w){
	return bigIntegerToString(w).c_str();
}
