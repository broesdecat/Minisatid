/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef AGGPRINT_HPP_
#define AGGPRINT_HPP_

#include <vector>
#include "utils/Print.hpp"

namespace MinisatID {
class TypedSet;
class Agg;
class Watch;

void printWatches(int verbosity, const std::vector<std::vector<Watch*> >& tempwatches);

void print(int verbosity, const TypedSet&, bool endl = false);
void print(int verbosity, const Agg& c, bool endl = false);

template<class T>
void NoSupportForBothSignInProductAgg(T& stream, const std::string& one, const std::string& two){
	stream <<"Product aggregates in which both the literal and its negation occur "
			"are currently not supported. Replace ";
	stream <<one <<"or " <<two <<"by a tseitin.\n";
	stream.flush();
}

}

#endif /* AGGPRINT_HPP_ */
