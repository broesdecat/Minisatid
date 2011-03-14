/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef PRINT_HPP_
#define PRINT_HPP_

#include <iostream>
#include "utils/Utils.hpp"
#include "utils/PrintMessage.hpp"

namespace Minisat{
	class Solver;
}

/**
 * Verbosity rules:
 * level 0: no output
 * level 1: statistics information
 * level 2: initialization information + ?
 * TODO
 */

namespace MinisatID {

namespace Print {

int getPrintableVar(Var v);

template<class T>
T& operator<<(T& stream, const Lit& lit){
	stream <<(sign(lit)?"-":"") <<getPrintableVar(var(lit));
	return stream;
}

template<class T>
void print(T& stream, const Lit& lit){
	stream <<(sign(lit)?"-":"") <<getPrintableVar(var(lit));
}

template<class T>
void print(const T& lit, const lbool val);

template<class S>
void print(S * const s);

template<class C>
void print(const C& c);

template<class S>
void print(rClause c, const S& s);

template<class T>
void printStatistics(T obj, int v = 1000){
	if(v>=1){
		obj->printStatistics();
	}
}

}

}

#endif /* PRINT_HPP_ */
