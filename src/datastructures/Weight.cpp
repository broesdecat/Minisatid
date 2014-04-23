/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "external/Weight.hpp"
#include "utils/NumericLimits.hpp"

#include <string>
#include <iostream>
#include <sstream>
#include <limits>
#include <cmath>

using namespace std;
using namespace MinisatID;

typedef numeric_limits<int> lim;

#ifdef GMP
int Weight::toInt() const {
	if(inf || w>getMaxElem<int>() || w<getMinElem<int>()) {
		throw idpexception("Invalid conversion of an arbitrary size number to int.");
	}
	return w.get_si();
}
int MinisatID::toInt(const Weight& w) {
	if(w>=Weight(getMaxElem<int>())){
		throw idpexception("Invalid conversion of an arbitrary size number to int.");
	}else if(w <= getMinElem<int>()){
		throw idpexception("Invalid conversion of an arbitrary size number to int.");
	}else{
		return w.toInt();
	}
}

std::string Weight::get_str() const {
	if(!inf) {
		return w.get_str();
	} else {
		return pos?"+oo":"-oo";
	}
}

bool MinisatID::isPosInfinity(const Weight& w){
	return w.isPosInfinity();
}
bool MinisatID::isNegInfinity(const Weight& w){
	return w.isNegInfinity();
}

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

string MinisatID::toString(const Weight& w) {
	return w.get_str();
}

Weight MinisatID::abs(const Weight& w) {return w<0?-w:w;}
Weight MinisatID::posInfinity() {return Weight(true);}
Weight MinisatID::negInfinity() {return Weight(false);}

Weight MinisatID::ceildiv(const Weight& l, const Weight& r){
	return l.ceildiv(r);
}

Weight MinisatID::floordiv(const Weight& l, const Weight& r){
	return l.floordiv(r);
}
#else //USING FINITE PRECISION WEIGHTS
string MinisatID::toString(const Weight& w) {
	stringstream s;
	s << w;
	return s.str();
}
Weight MinisatID::posInfinity() {
	return lim::max();
}
Weight MinisatID::negInfinity() {
	return lim::min();
}
int MinisatID::toInt(const Weight& weight) {
	return weight;
}
Weight MinisatID::ceildiv(const Weight& l, const Weight& r) {
	return ceil(((double) l) / r);
}
Weight MinisatID::floordiv(const Weight& l, const Weight& r) {
	return floor(((double) l) / r);
}
bool MinisatID::isPosInfinity(const Weight& w){
	return w==posInfinity();
}
bool MinisatID::isNegInfinity(const Weight& w){
	return w==negInfinity();
}
#endif
