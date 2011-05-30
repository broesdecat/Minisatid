/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mari�n, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PCLOGGER_HPP_
#define PCLOGGER_HPP_

#include <vector>
#include <assert.h>
#include "utils/Utils.hpp"

namespace MinisatID {
class SearchMonitor{
private:
	std::vector<int> occurrences;
	int propagations;

public:
	SearchMonitor(){}

	void addPropagation() { ++propagations; }
	int getNbPropagations() const { return propagations; }
	void addCount(Var v){
		assert(v>=0);
		unsigned int var(v);
		if((var+1)>occurrences.size()){
			occurrences.resize(var+1, 0);
		}
		++occurrences[var];
	}
	int getCount(Var v) const{
		assert(v>=0);
		return (uint)v>occurrences.size()?0:occurrences.at((uint)v);
	}

};
}

#endif /* PCLOGGER_HPP_ */
