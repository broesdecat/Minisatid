#include "AggTypes.hpp"
#include "cstdlib"

template <typename T>
string printWeight(const T& w){
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
