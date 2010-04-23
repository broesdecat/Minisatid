/*
 * solverfwd.h
 *
 *  Created on: Mar 20, 2010
 *      Author: broes
 */

#ifndef SOLVERFWD_H_
#define SOLVERFWD_H_

/*#include <boost/smart_ptr/shared_ptr.hpp>
#include <boost/smart_ptr/weak_ptr.hpp>
#include <boost/smart_ptr/enable_shared_from_this.hpp>*/

#include <tr1/memory>

#include "SolverTypes.h"
#include "IDTypes.h"
#include "AggTypes.h"
#include "debug.h"

class ParseExc: public std::exception{
public:
	virtual const char* what() const throw(){
		return "Parse exception";
	}
};
class NoDefAllowedExc: public ParseExc{
public:
	virtual const char* what() const throw(){
		return "Definition found but not definition allowed by header";
	}
};
class NoAggrAllowedExc: public ParseExc{
public:
	virtual const char* what() const throw(){
		return "Aggregate found but not aggregates allowed by header";
	}
};

class UNSAT: public std::exception {
public:
	virtual const char* what() const throw(){
		return "UNSAT exception";
	}
};

extern int verbosity;

enum MINIM {MNMZ, SUBSETMNMZ, SUMMNMZ, NONE};

enum POLARITY	{ polarity_true = 0, polarity_false = 1, polarity_stored = 2, polarity_rnd = 3 };

struct ECNF_mode {
	//minisat specific: TODO: initialize them on time!!!
	double random_var_freq, var_decay;
	POLARITY polarity_mode;
	int verbosity;
	//verbosity

	//rest

	bool def,aggr,mnmz; // True for those extensions that are being used.
	IDSEM sem;
	int nbmodels;	//Find at least this number of models. If there are less models,
					//UNSAT will be returned (after finding the existing number)
	FINDCS		defn_strategy;      // Controls which propagation strategy will be used for definitions.                         (default always)
	MARKDEPTH	defn_search;        // Controls which search type will be used for definitions.                                  (default include_cs)
	SEARCHSTRAT	ufs_strategy;		//Which algorithm to use to find unfounded sets

	ECNF_mode() :
		random_var_freq(0.02), var_decay(1 / 0.95), polarity_mode(polarity_stored),
		def(false), aggr(false), mnmz(false), sem(WELLF), nbmodels(1),
		defn_strategy(always), defn_search(include_cs), ufs_strategy(breadth_first){}
};
extern ECNF_mode modes;

#endif /* SOLVERFWD_H_ */
