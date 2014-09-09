/***********************************************************************************[SolverTypes.h]
 Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 Copyright (c) 2007-2010, Niklas Sorensson

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#pragma once

#include <vector>
#include "MAssert.hpp"

namespace MinisatID {

typedef int Atom;

struct VarID{
	unsigned int id;

	bool operator ==(VarID p) const {
		return id == p.id;
	}
	bool operator !=(VarID p) const {
		return id != p.id;
	}
	bool operator <(VarID p) const {
		return id < p.id;
	}
};

struct Lit {
	int x;

	bool operator ==(Lit p) const {
		return x == p.x;
	}
	bool operator !=(Lit p) const {
		return x != p.x;
	}
	bool operator <(Lit p) const {
		return x < p.x;
	} // '<' makes p, ~p adjacent in the ordering.

	bool hasSign() const {
		return x & 1;
	}
	Atom getAtom() const {
		return x >> 1;
	}
};

inline Lit mkLit(Atom var, bool sign = false) {
	MAssert(var>=0);
	Lit p;
	p.x = var + var + (int) sign;
	return p;
}

inline Lit operator ~(Lit p) {
	Lit q;
	q.x = p.x ^ 1;
	return q;
}
inline Lit operator !(Lit p) {
	Lit q;
	q.x = p.x ^ 1;
	return q;
}
inline bool sign(Lit p) {
	return p.x & 1;
}
inline int var(Lit p) {
	return p.x >> 1;
}

// Mapping Literals to and from compact integers suitable for array indexing:
inline int toInt(Lit p) {
	return p.x;
}
// Returns an integer which represents this literal: abs(x) is the atom, x<0 is the sign
inline int getIntLit(Lit p) { return var(p)* (sign(p)?-1:1); }

bool isPositive(const Lit& lit);
bool isNegative(const Lit& lit);

typedef std::vector<Lit> litlist;
typedef std::vector<Atom> varlist;
inline Lit  mkPosLit	(Atom var) 	{ return mkLit(var, false); }
inline Lit  mkNegLit	(Atom var) 	{ return mkLit(var, true); }

}

// To use Lit in an unordered_map, a hash function had to be defined in namespace std
namespace std {

template<>
struct hash<MinisatID::Lit> {
	size_t operator()(const MinisatID::Lit& t) const {
		return (size_t) t.x;
	}
};

}
