/*
 * solverfwd.h
 *
 *  Created on: Mar 20, 2010
 *      Author: broes
 */

#ifndef SOLVERFWD_H_
#define SOLVERFWD_H_

#include <boost/smart_ptr/shared_ptr.hpp>
#include <boost/smart_ptr/weak_ptr.hpp>
#include <boost/smart_ptr/enable_shared_from_this.hpp>

#include "SolverTypes.h"
#include "idsolvertypes.h"
#include "AggTypes.h"

class ParseExc: public std::exception{ };
class NoDefAllowedExc: public ParseExc{ };
class NoAggrAllowedExc: public ParseExc{ };

class UNSAT: public std::exception { };

extern int verbosity;

enum MINIM {MNMZ, SUBSETMNMZ, SUMMNMZ, NONE};

struct ECNF_mode {
	bool def,aggr,mnmz; // True for those extensions that are being used.
	IDSEM sem;
	int nbmodels;	//Find at least this number of models. If there are less models,
					//UNSAT will be returned (after finding the existing number)
	FINDCS		defn_strategy;      // Controls which propagation strategy will be used for definitions.                         (default always)
	MARKDEPTH	defn_search;        // Controls which search type will be used for definitions.                                  (default include_cs)
	SEARCHSTRAT	ufs_strategy;		//Which algorithm to use to find unfounded sets

	ECNF_mode() :
		def(false), aggr(false), mnmz(false), sem(WELLF), nbmodels(1),
		defn_strategy(always), defn_search(include_cs), ufs_strategy(breadth_first){}
};
extern ECNF_mode modes;

#endif /* SOLVERFWD_H_ */
