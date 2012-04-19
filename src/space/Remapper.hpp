/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef REMAPPER_HPP_
#define REMAPPER_HPP_

#include <unordered_map>
#include <iostream>
#include "external/ExternalUtils.hpp"

namespace MinisatID{

typedef std::unordered_map<int, int> atommap;

class Remapper{
protected:
	int maxnumber;
public:
	Remapper(): maxnumber(0){}
	Var		largestVar	() const { return maxnumber; }
private:
	//Maps from NON-INDEXED to INDEXED atoms
	atommap 		origtocontiguousatommapper, contiguoustoorigatommapper;

	void checkVar(const Atom& atom){
		if(atom<1 || atom == std::numeric_limits<int>::max()){
			throw idpexception(">>> Variables can only be numbered starting from 1 and not be equal to max-int.\n");
		}
	}

public:
	Var getVar(const Atom& atom){
		checkVar(atom);

		auto i = origtocontiguousatommapper.find(atom);
		Var v = 0;
		if(i==origtocontiguousatommapper.cend()){
			origtocontiguousatommapper.insert({atom, maxnumber});
			contiguoustoorigatommapper.insert({maxnumber, atom});
			v = maxnumber++;
		}else{
			v = (*i).second;
		}
		return v;
	}

	Var getNewVar(){
		return maxnumber++;
	}

	bool wasInput(const Lit& lit) const {
		return contiguoustoorigatommapper.find(var(lit))!=contiguoustoorigatommapper.cend();
	}

	// NOTE: if newvar was called internally, it cannot be mapped back to input (and shouldn't).
	Literal getLiteral(const Lit& lit) const{
		auto atom = contiguoustoorigatommapper.find(var(lit));
		MAssert(atom!=contiguoustoorigatommapper.cend());
		int origatom = (*atom).second;
		return mkLit(origatom, sign(lit));
	}
};

}

#endif /* REMAPPER_HPP_ */
