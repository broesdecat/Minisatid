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

typedef std::unordered_map<uint, uint> idmap;

class Remapper{
protected:
	uint maxnumber; // NOTE: guaranteed not to be larger than max<int>
public:
	Remapper(): maxnumber(0){}
	uint		largestID	() const { return maxnumber; }
private:
	//Maps from NON-INDEXED to INDEXED ids
	idmap origtocontiguousatommapper, contiguoustoorigatommapper;

	void checkVar(uint atom){
		if(atom >= (uint)std::numeric_limits<int>::max()){
			throw idpexception(">>> Variables cannot be larger to or equal than to max-int.\n");
		}
	}

public:
	Atom getVar(const Atom& atom){
		if(atom <1 ){
			throw idpexception(">>> Variables can only be numbered starting from 1.\n");
		}
		return (int)getID(atom);
	}
	uint getID(uint id){
		checkVar(id);

		auto i = origtocontiguousatommapper.find(id);
		uint v = 0;
		if(i==origtocontiguousatommapper.cend()){
			origtocontiguousatommapper.insert({id, maxnumber});
			contiguoustoorigatommapper.insert({maxnumber, id});
			v = getNewID();
		}else{
			v = (*i).second;
		}
		return v;
	}

	Atom getNewVar(){
		return getNewID();
	}
	uint getNewID(){
		if(maxnumber==(uint)std::numeric_limits<int>::max()){ // Overflow check
			throw idpexception("Cannot create additional variables.");
		}
		return maxnumber++;
	}

	bool wasInput(const Lit& lit) const {
		auto v = var(lit);
		MAssert(v>=0);
		return wasInput((uint)v);
	}

	bool wasInput(VarID id) const {
		return wasInput(id.id);
	}

	bool wasInput(uint id) const {
		return contiguoustoorigatommapper.find(id)!=contiguoustoorigatommapper.cend();
	}

	// NOTE: if newvar was called internally, it cannot be mapped back to input (and shouldn't).
	Lit getLiteral(const Lit& lit) const{
		auto v = var(lit);
		MAssert(v>=1);
		auto origatom = (int)getOrigID((uint)v);
		return mkLit(origatom, sign(lit));
	}
	VarID getOrigID(VarID id) const{
		return {getOrigID(id.id)};
	}
	uint getOrigID(uint id) const{
		auto origidit = contiguoustoorigatommapper.find(id);
		MAssert(origidit!=contiguoustoorigatommapper.cend());
		return origidit->second;
	}
};

}

#endif /* REMAPPER_HPP_ */
