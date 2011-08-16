/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef WEIGHT_HPP_
#define WEIGHT_HPP_

#include <string>
#include <limits>
#include <cassert>

// Weight declaration and utilities

#ifdef GMP
	#include "gmpxx.h"

	namespace MinisatID {
	class Weight{
	private:
		mpz_class w;
		bool inf, pos;
	public:
		Weight(): w(0), inf(false), pos(false){}
		Weight(int i): w(i), inf(false), pos(false){}
		Weight(long i): w(i), inf(false), pos(false){}
		Weight(mpz_class w): w(w), inf(false), pos(false){}
		Weight(bool posinf): w(0), inf(true), pos(posinf){}

		int toInt() const { assert(not inf && w<=std::numeric_limits<int>::max() && w>=std::numeric_limits<int>::min()); return w.get_si(); }

		operator const mpz_class&() const { assert(!inf); return w; }

		friend std::istream& operator>>(std::istream& input, Weight& obj);

		std::string get_str() const{
			if(!inf){
				return w.get_str();
			}else{
				return pos?"+inf":"-inf";
			}
		}

		const Weight operator-() const {
			Weight w2(*this);
			w2.w = -w2.w;
			w2.pos=!w2.pos;
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
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			}else{
				w += rhs.w;
			}
			return *this;
		}

		Weight& operator-=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:!rhs.pos;
				inf = true;
			}else{
				w -= rhs.w;
			}
			return *this;
		}

		Weight& operator*=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				w=0;
				pos = inf?pos:rhs.pos;
				inf = true;
			}else{
				w *= rhs.w;
			}
			return *this;
		}

		Weight& operator/=(const Weight &rhs) {
			if(rhs.inf || inf){
				assert(!rhs.inf || !inf);
				if(inf){
					if(rhs.w<0){
						pos = !pos;
					}
				}else{
					w = 0;
					inf = false;
				}
			}else{
				w /= rhs.w;
			}
			return *this;
		}

		bool operator==(const Weight& weight) const{
			return w==weight.w && inf==weight.inf && pos==weight.pos;
		}

		bool operator!=(const Weight& weight) const{
			return !(*this==weight);
		}

		bool operator<(const Weight& weight) const {
			if(!inf && !weight.inf){
				return w < weight.w;
			}else if(inf){
				if(weight.inf){
					return false;
				}else{
					return !pos;
				}
			}else{//only weight is inf
				return weight.pos;
			}
		}

		bool operator<=(const Weight& weight) const{
			return *this==weight || *this<weight;
		}

		bool operator>(const Weight& weight) const{
			return !(*this<=weight);
		}

		bool operator>=(const Weight& weight) const{
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
	typedef int Weight;
	//FAST, NO OVERFLOW SUPPORT
	}
#endif

namespace MinisatID {

	Weight posInfinity();
	Weight negInfinity();

	std::string toString(const Weight& w);
	int toInt(const Weight& weight);
}

#endif /* WEIGHT_HPP_ */
