/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include <string>
#include <limits>
#include <iostream>
#include "MAssert.hpp"
#include "Idpexception.hpp"

// Weight declaration and utilities

#ifdef GMP
#include "gmpxx.h"

namespace MinisatID {
	class Weight {
	private:
		mpz_class w;
		bool inf, pos;
	public:
		Weight(): w(0), inf(false), pos(false) {}
		Weight(int i): w(i), inf(false), pos(false) {}
		Weight(long i): w(i), inf(false), pos(false) {}
		Weight(double i): w(i), inf(false), pos(false) {}
		Weight(mpz_class w): w(w), inf(false), pos(false) {}
		Weight(bool posinf): w(0), inf(true), pos(posinf) {}

		int toInt() const;

		operator const mpz_class&() const {MAssert(!inf); return w;}

		friend std::istream& operator>>(std::istream& input, Weight& obj);

		std::string get_str() const;

		explicit operator int() const { return toInt(); }

		bool isPosInfinity() const {
			return pos and inf;
		}
		bool isNegInfinity() const {
			return not pos and inf;
		}

		const Weight operator-() const {
			Weight w2(*this);
			w2.w = -w2.w;
			if(inf){
				w2.pos=!w2.pos;
			}
			return w2;
		}

		const Weight operator-(const Weight &other) const {
			return Weight(*this) -= other;
		}

		const Weight operator+(const Weight &other) const {
			return Weight(*this) += other;
		}

		const Weight operator*(const Weight &other) const {
			return Weight(*this) *= other;
		}

		const Weight operator/(const Weight &other) const {
			return Weight(*this) /= other;
		}

		Weight& operator+=(const Weight &rhs) {
			if(rhs.inf || inf) {
				MAssert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			} else {
				w += rhs.w;
			}
			return *this;
		}

		Weight& operator-=(const Weight &rhs) {
			if(rhs.inf || inf) {
				MAssert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:!rhs.pos;
				inf = true;
			} else {
				w -= rhs.w;
			}
			return *this;
		}

		Weight& operator*=(const Weight &rhs) {
			if(rhs.inf || inf) {
				MAssert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			} else {
				w *= rhs.w;
			}
			return *this;
		}

		Weight& operator/=(const Weight &rhs) {
			if(rhs.inf || inf) {
				MAssert(!rhs.inf || !inf);
				if(inf) {
					if(rhs.w<0) {
						pos = !pos;
					}
				} else {
					w = 0;
					inf = false;
					pos = false;
				}
			} else {
				w /= rhs.w;
			}
			return *this;
		}

		Weight ceildiv(const Weight& rhs) const {
			mpz_class q;
			mpz_cdiv_q(q.get_mpz_t(),w.get_mpz_t(),rhs.w.get_mpz_t());
			return Weight(q);
		}

		Weight floordiv(const Weight& rhs) const {
			mpz_class q;
			mpz_fdiv_q(q.get_mpz_t(),w.get_mpz_t(),rhs.w.get_mpz_t());
			return Weight(q);
		}

		Weight& operator++() {
			operator+=(1);
			return *this;
		}

		Weight& operator--() {
			operator-=(1);
			return *this;
		}

		bool operator==(const Weight& weight) const {
			return w==weight.w && inf==weight.inf && pos==weight.pos;
		}

		bool operator!=(const Weight& weight) const {
			return !(*this==weight);
		}

		bool operator<(const Weight& weight) const {
			if(!inf && !weight.inf) {
				return w < weight.w;
			} else if(inf) {
				if(weight.inf) {
					return false;
				} else {
					return !pos;
				}
			} else { //only weight is inf
				return weight.pos;
			}
		}

		bool operator<=(const Weight& weight) const {
			return *this==weight || *this<weight;
		}

		bool operator>(const Weight& weight) const {
			return !(*this<=weight);
		}

		bool operator>=(const Weight& weight) const {
			return !(*this<weight);
		}
	};
	Weight abs(const Weight& w);
	std::istream& operator>>(std::istream& input, Weight& obj);
	std::ostream& operator<<(std::ostream& output, const Weight& p);
}

#else

namespace MinisatID {
#define NOARBITPREC

typedef long long Weight;
//FAST, NO OVERFLOW SUPPORT
}

#endif

namespace MinisatID {
	Weight posInfinity();
	Weight negInfinity();

	std::string toString(const Weight& w);
	int toInt(const Weight& weight); // Throws if it was not an int
	Weight ceildiv(const Weight& l, const Weight& r);
	Weight floordiv(const Weight& l, const Weight& r);
	bool isPosInfinity(const Weight& w);
	bool isNegInfinity(const Weight& w);
}
