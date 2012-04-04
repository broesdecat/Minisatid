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

#ifndef Basic_Minisat_SolverTypes_h
#define Basic_Minisat_SolverTypes_h

namespace Minisat {

typedef int Var;
const Var var_Undef = { -1 };

struct Lit {
	int x;

	// Use this as a constructor:
	friend Lit mkLit(Var var, bool sign = false);

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
	Var getAtom() const {
		return x >> 1;
	}
};

inline Lit mkLit(Var var, bool sign) {
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

const Lit lit_Undef = { -2 }; // }- Useful special constants.
const Lit lit_Error = { -1 }; // }
}

#endif
