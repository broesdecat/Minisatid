//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
Copyright (c) 2006-2009, Maarten Mariën

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

#ifndef AGGTYPES_H
#define AGGTYPES_H

#include <limits>
#include <set>
#include <iostream>

#include "solvers/utils/Utils.hpp"

#ifdef USEMINISAT22
using namespace Minisat;
#endif

namespace Aggrs{
class Agg;
class AggSet;
typedef Agg* pAgg;
typedef vector<pAgg> lsagg;
typedef AggSet* pSet;

class WLV;
typedef vector<WLV> lwlv;

class PropagationInfo;
typedef vector<PropagationInfo> lprop;

enum Occurrence {HEAD, POS, NEG};

class WLit {  // Weighted literal
private:
	Lit lit;
	Weight weight;

public:
    explicit WLit(const Lit& l, const Weight& w) : lit(l), weight(w) {}

    const Lit& 		getLit() 	const { return lit; }
    const Weight&	getWeight() const { return weight; }

    bool operator<	(const WLit& p)		 const { return weight < p.weight; }
    bool operator<	(const Weight& bound)const { return weight < bound; }
    bool operator==	(const WLit& p)		 const { return weight == p.weight && lit==p.lit; }
};

class WLV: public WLit{
private:
	lbool value;

public:
	explicit WLV(const Lit& l, const Weight& w, lbool value) : WLit(l, w), value(value) {}

	lbool	getValue() const 	{ return value; }
	void	setValue(lbool v) 	{ value = v; }
};

class PropagationInfo {	// Propagated literal
private:
	WLV wlv;
	Occurrence  type;		// POS if the literal in the set became true, NEG otherwise
							//		(and HEAD if the head was propagated)
	Weight prevcertain, prevpossible; //values BEFORE the propagation was added

public:
    PropagationInfo(const Lit& l, const Weight& w, Occurrence t, const Weight& pc, const Weight& pv) :
    	wlv(l, w, l_Undef), type(t), prevcertain(pc), prevpossible(pv) {}

    const Lit& 			getLit()	const { return wlv.getLit(); }
    const Weight&		getWeight()	const { return wlv.getWeight(); }
    const WLV&			getWLV()	const { return wlv; }
    const Occurrence& 	getType() 	const { return type; }
    const Weight& 		getPC()		const { return prevcertain; }
    const Weight& 		getPP()		const { return prevpossible; }
};
}

#endif /*AGGTYPES_H*/
