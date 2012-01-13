/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include <cmath>

#include "gtest/gtest.h"

#include "utils/Utils.hpp"

using namespace std;
using namespace MinisatID;

namespace Tests{
	int Factorial(int n){
		if(n<=1){
			return 1;
		}else{
			return n*Factorial(n-1);
		}
	}

	bool IsPrime(int n){
		if(n<1){
			return false;
		}else if(n==1){
			return false;
		}

		int test = 2;
		while(test<=sqrt(n)){
			if(n%test==0){
				return false;
			}
			test++;
		}
		return true;
	}

	// Tests Factorial().

	// Tests factorial of negative numbers.
	TEST(FactorialTest, Negative) {
	  // This test is named "Negative", and belongs to the "FactorialTest"
	  // test case.
	  EXPECT_EQ(1, Factorial(-5));
	  EXPECT_EQ(1, Factorial(-1));
	  EXPECT_TRUE(Factorial(-10) > 0);

	  // <TechnicalDetails>
	  //
	  // EXPECT_EQ(expected, actual) is the same as
	  //
	  //   EXPECT_TRUE((expected) == (actual))
	  //
	  // except that it will print both the expected value and the actual
	  // value when the assertion fails.  This is very helpful for
	  // debugging.  Therefore in this case EXPECT_EQ is preferred.
	  //
	  // On the other hand, EXPECT_TRUE accepts any Boolean expression,
	  // and is thus more general.
	  //
	  // </TechnicalDetails>
	}

	// Tests factorial of 0.
	TEST(FactorialTest, Zero) {
	  EXPECT_EQ(1, Factorial(0));
	}

	// Tests factorial of positive numbers.
	TEST(FactorialTest, Positive) {
	  EXPECT_EQ(1, Factorial(1));
	  EXPECT_EQ(2, Factorial(2));
	  EXPECT_EQ(6, Factorial(3));
	  EXPECT_EQ(40320, Factorial(8));
	}


	// Tests IsPrime()

	// Tests negative input.
	TEST(IsPrimeTest, Negative) {
	  // This test belongs to the IsPrimeTest test case.

	  EXPECT_FALSE(IsPrime(-1));
	  EXPECT_FALSE(IsPrime(-2));
	  EXPECT_FALSE(IsPrime(INT_MIN));
	}

	// Tests some trivial cases.
	TEST(IsPrimeTest, Trivial) {
	  EXPECT_FALSE(IsPrime(0));
	  EXPECT_FALSE(IsPrime(1));
	  EXPECT_TRUE(IsPrime(2));
	  EXPECT_TRUE(IsPrime(3));
	}

	// Tests positive input.
	TEST(IsPrimeTest, Positive) {
	  EXPECT_FALSE(IsPrime(4));
	  EXPECT_TRUE(IsPrime(5));
	  EXPECT_FALSE(IsPrime(6));
	  EXPECT_TRUE(IsPrime(23));
	}
}


int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
