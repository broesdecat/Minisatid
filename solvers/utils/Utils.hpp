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

#include "solvers/SATUtils.h"
#include "solvers/external/ExternalUtils.hpp"

#include <tr1/memory>

namespace MinisatID {

typedef std::vector<void*>::size_type vsize;

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

///////
// SOLUTION DATASTRUCTURE
///////

class InternSol{
private:
	const bool printmodels, savemodels;
	bool nomoremodels;
	const int nbmodelstofind;
	int nbmodelsfound;
	vec<vec<Lit> > models;
	vec<Lit> assumptions;

public:
	InternSol(bool print, bool save, int searchnb, const vec<Lit>& assumpts):
			printmodels(print), savemodels(save),
			nbmodelstofind(searchnb){
		for(int i=0; i<assumpts.size(); i++){
			assumptions.push(assumpts[i]);
		}
	}
	~InternSol(){};

	void addModel(vec<Lit> model) {;}
	const vec<vec<Lit> >& getModels() { if(!savemodels){ throw idpexception("Models were not being saved!\n");} return models; }
	int modelCount() { return nbmodelsfound; }
};

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

    operator 	Lit()	const { return lit; }
    operator Weight()	const { return weight; }
};

#define reportf(...) ( fflush(stdout), fprintf(stderr, __VA_ARGS__), fflush(stderr) )

inline int gprintVar(Var v){
	return v+1;
}

inline void gprintLit(const Lit& l, const lbool val){
	reportf("%s%d:%c", (sign(l) ? "-" : ""), gprintVar(var(l)), (val == l_True ? '1' : (val == l_False ? '0' : 'X')));
}

inline void gprintLit(const Lit& l){
	reportf("%s%d", (sign(l) ? "-" : ""), gprintVar(var(l)));
}

inline void gprintClause(const vec<Lit>& c){
	for(int i=0; i<c.size(); i++){
		gprintLit(c[i]); reportf(" ");
	}
}

}

#endif /* UTILS_H_ */
