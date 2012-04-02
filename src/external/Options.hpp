/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MINISATID_OPTIONS_HPP_
#define MINISATID_OPTIONS_HPP_

#include <string>
#include <ostream>

namespace MinisatID{

// Definitional options
enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
											// when a guaranteed cycle-free justification is used!
enum DEFSEARCHSTRAT { breadth_first /*, depth_first*/ }; // Unfounded set search strategy
enum DEFSEM { DEF_STABLE, DEF_WELLF, DEF_COMP }; 	// Definitional semantics

enum class SATVAL { UNSAT, POS_SAT};
SATVAL operator&= (SATVAL orig, SATVAL add);

enum class Polarity {
	TRUE, FALSE, STORED, RAND
}; // SAT-solver polarity option

enum class InputFormat 	{ FODOT, ASP, OPB};
enum class OutputFormat { FODOT, ASP, PLAIN, FZ, OPB, DEFAULT };
enum class Inference	{ PROPAGATE, MODELEXPAND, PRINTTHEORY, PRINTGRAPH };

// General options for all inferences
class SolverOption {
		//TODO prevent unauthorised access by getters and setters (e.g. primesfile should NEVER be accessed directly)
public:
	Inference		inference;
	InputFormat 	format;
	OutputFormat 	transformat;
	int 			verbosity;
	int 			randomseed;
	int 			nbmodels;
	DEFSEM 			defsem;
	DEFSEARCHSTRAT 	ufs_strategy;
	DEFFINDCS 		defn_strategy;
	DEFMARKDEPTH 	defn_search;
	bool			checkcyclefreeness;
	int 			idclausesaving, aggclausesaving;
	bool 			selectOneFromUFS;
	bool 			tocnf;
	double			watchesratio;
	bool			useaggheur;
	std::string 	primesfile;
	//bool 			remap;
	double 			rand_var_freq, var_decay;
	Polarity 		polarity;
	bool 			bumpaggonnotify, bumpidonstart;
	bool			asapaggprop;
	long 			ufsvarintrothreshold;
	bool			subsetminimizeexplanation, currentlevelfirstinexplanation, innogoodfirstinexplanation;
	bool			lazy;
	std::string		outputfile;

	SolverOption();

	bool 		verifyOptions() const;
	std::string	getPrimesFile() const;
	void print(std::ostream& stream) const;
};

enum class Models	{ALL, BEST, NONE};

class ModelExpandOptions{
public:
	Models			printmodels;
	Models			savemodels;
	int 			nbmodelstofind;

	ModelExpandOptions():
			printmodels(Models::BEST), savemodels(Models::NONE),
			nbmodelstofind(0){
	}
};

}

#endif /* MINISATID_OPTIONS_HPP_ */
