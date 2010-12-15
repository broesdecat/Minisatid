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

#ifndef UTILS_H_
#define UTILS_H_

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <map>
#include <string>

#include "satsolver/SATUtils.hpp"
#include "external/ExternalUtils.hpp"

#include <tr1/memory>

namespace MinisatID {

// General vector size type usable for any POINTER types!
typedef std::vector<void*>::size_type vsize;

bool isPositive(Lit l);
Lit createNegativeLiteral(Var i);
Lit createPositiveLiteral(Var i);

///////
// Internal weighted literal
///////

class WL {  // Weighted literal
private:
	Lit lit;
	Weight weight;

public:
    explicit WL(const Lit& l, const Weight& w) : lit(l), weight(w) {}

    const Lit& 		getLit() 	const { return lit; }
    const Weight&	getWeight() const { return weight; }

    bool operator<	(const WL& p)		 const { return weight < p.weight; }
    bool operator<	(const Weight& bound)const { return weight < bound; }
    bool operator==	(const WL& p)		 const { return weight == p.weight && lit==p.lit; }
};

//Compare WLs by their literals, placing same literals next to each other
bool compareWLByLits(const WL& one, const WL& two);
//Compare WLs by their weights
bool compareWLByWeights(const WL& one, const WL& two);

///////
// Debug information
///////

inline int gprintVar(Var v){
	return v+1;
}

inline void gprintLit(const Lit& l, const lbool val){
	report("%s%d:%c", (sign(l) ? "-" : ""), gprintVar(var(l)), (val == l_True ? '1' : (val == l_False ? '0' : 'X')));
}

inline void gprintLit(const Lit& l){
	report("%s%d", (sign(l) ? "-" : ""), gprintVar(var(l)));
}

inline void gprintClause(const vec<Lit>& c){
	for(int i=0; i<c.size(); i++){
		gprintLit(c[i]); report(" ");
	}
}

///////
// Support for deleting lists of pointer elements
///////

template<class T>
void deleteList(std::vector<T*> l){
	for(class std::vector<T*>::const_iterator i=l.begin(); i!=l.end(); i++){
		if(*i!=NULL){
			delete(*i);
		}
	}
	l.clear();
}

template<class T>
void deleteList(std::vector<std::vector<T*> > l){
	for(class std::vector<std::vector<T*> >::const_iterator i=l.begin(); i!=l.end(); i++){
		deleteList(*i);
	}
	l.clear();
}

template<class T, class K>
void deleteList(std::map<K, T*> l){
	for(class std::map<K, T*>::const_iterator i=l.begin(); i!=l.end(); i++){
		if((*i).second!=NULL){
			delete((*i).second);
		}
	}
	l.clear();
}

}

#endif /* UTILS_H_ */
