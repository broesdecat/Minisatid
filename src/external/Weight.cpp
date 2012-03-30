/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "external/Weight.hpp"

#include <string>
#include <sstream>
#include <limits>

using namespace std;
using namespace MinisatID;

typedef numeric_limits<int> lim;

#ifdef GMP
	ostream& MinisatID::operator<<(ostream& output, const Weight& p) {
		output << p.get_str();
		return output;
	}

	istream& MinisatID::operator>>(istream& input, Weight& obj) {
		long n;
		input >> n;
		obj.w = n;
		return input;
	}

	string MinisatID::toString(const Weight& w){
		return w.get_str();
	}

	Weight MinisatID::abs(const Weight& w) { return w<0?-w:w; }
	Weight MinisatID::posInfinity() { return Weight(true); }
	Weight MinisatID::negInfinity() { return Weight(false); }

	int MinisatID::toInt(const Weight& weight) { return toInt(weight); }
#else //USING FINITE PRECISION WEIGHTS
	string MinisatID::toString(const Weight& w){
		stringstream s;
		s <<w;
		return s.str();
	}
	Weight MinisatID::posInfinity() { return lim::max(); }
	Weight MinisatID::negInfinity() { return lim::min(); }
	int MinisatID::toInt(const Weight& weight) { return weight; }
#endif