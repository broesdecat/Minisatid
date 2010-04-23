/*
 * debug.h
 *
 *  Created on: Mar 20, 2010
 *      Author: broes
 */

#ifndef DEBUG_H_
#define DEBUG_H_

#include "SolverTypes.h"
#include "stdio.h"

/******************
 * DEBUGGING INFO *
 ******************/

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

void noMoreMem();

#endif /* DEBUG_H_ */
