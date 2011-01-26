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

#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <string>

#include <map>
#include <vector>
#include <string>
#include <cstdlib>

#include "GeneralUtils.hpp"

namespace MinisatID {

///////
// Generic atom and literal structures
///////

class Atom{
private:
	int atom; //Important: because of mutual exclusion of const members and a clean assignment operator, i did not make this constant, but semantically it should be

public:
	explicit Atom(int a): atom(a){ }
	int		getValue	() 				const { return atom; }

	bool operator==	(const Atom& a) const { return atom==a.atom; }
	bool operator<	(const Atom& a) const { return atom<a.atom; }
};

class Literal{
private:
	int lit;

public:
	//@pre: a is positive
	explicit Literal(int a, bool s = false): lit(s?-a:a){ assert(a>=0); }
	explicit Literal(Atom a, bool s = false): lit(s?-a.getValue():a.getValue()){ assert(a.getValue()>=0); }

	int		getValue()						const { return lit; }
	Atom 	getAtom() 						const { return Atom(lit<0?-lit:lit); }
	bool 	hasSign() 						const { return lit<0; }
	bool 	operator== (const Literal& l) 	const { return lit == l.lit; }
	bool 	operator< (const Literal& l) 	const {	return abs(lit) < abs(l.lit); }
	Literal operator~()						const { return Literal(getAtom(), lit>0?true:false); }
};

// A class representing a tuple of a literal and an associated weight
struct WLtuple{
	const Literal l;
	const Weight w;

	WLtuple(const Literal& l, const Weight& w): l(l), w(w){ }
	WLtuple operator=(const WLtuple& lw) const { return WLtuple(lw.l, lw.w); }
};

///////
// Generic model expansion solution datastructure
///////

class Solution{
private:
	const bool 	printmodels, savemodels, search;
	//bool 		nomoremodels;
	const int 	nbmodelstofind;
	int 		nbmodelsfound;
	std::vector<std::vector<Literal> > 	models;
	const std::vector<Literal> 			assumptions;

public:
	Solution(bool print, bool save, bool search, int searchnb, const std::vector<Literal>& assumpts):
			printmodels(print), savemodels(save), search(search),
			nbmodelstofind(searchnb), nbmodelsfound(0),
			assumptions(assumpts){}
	~Solution(){};

	int 	getNbModelsFound	() const	{ return nbmodelsfound; }
	int 	getNbModelsToFind	() const	{ return nbmodelstofind; }
	bool 	getPrint			() const 	{ return printmodels; }
	bool 	getSave				() const 	{ return savemodels; }
	bool 	getSearch			() const 	{ return search; }

	void 	addModel			(std::vector<Literal> model) {
		nbmodelsfound++;
		if(getSave()){
			models.push_back(model);
		}
	}

	const std::vector<Literal>& getAssumptions	() { return assumptions; }

	/**
	 * IMPORTANT: only allowed when the models are being saved!
	 */
	const std::vector<std::vector<Literal> >& 	getModels		() {
		if(!savemodels) throw idpexception("Models were not being saved!\n");
		return models;
	}
};


}

#endif /*EXTERNALUTILS_HPP_*/
