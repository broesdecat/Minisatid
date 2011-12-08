/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef EXTERNALUTILS_HPP_
#define EXTERNALUTILS_HPP_

#include <string>

typedef unsigned int uint;

#include "Idpexception.hpp"
#include "Weight.hpp"
#include "Datastructures.hpp"
#include "LazyClauseSupport.hpp"
#include "TerminationManagement.hpp"

namespace MinisatID {
	// Definitional options
	enum DEFFINDCS { always, adaptive, lazy };	// Unfounded set search frequency
	enum DEFMARKDEPTH { include_cs };			// Originally also contained stop_at_cs, which is no longer correct
												// when a guaranteed cycle-free justification is used!
	enum DEFSEARCHSTRAT { breadth_first /*, depth_first*/ }; // Unfounded set search strategy
	enum DEFSEM { DEF_STABLE, DEF_WELLF, DEF_COMP }; 	// Definitional semantics

	enum class SATVAL { UNSAT, POS_SAT};
	SATVAL operator&= (SATVAL orig, SATVAL add);

	enum POLARITY {
		POL_TRUE,
		POL_FALSE,
		POL_STORED,
		POL_RAND
	}; // SAT-solver polarity option

	enum INPUTFORMAT 	{ FORMAT_FODOT, FORMAT_ASP, FORMAT_OPB};
	enum OUTPUTFORMAT 	{ TRANS_FODOT, TRANS_ASP, TRANS_PLAIN, TRANS_FZ, TRANS_OPB, TRANS_DEFAULT };
	enum Inference		{PROPAGATE, MODELEXPAND, PRINTTHEORY };

	// Structure containing general options for the solvers
	class SolverOption {
			//TODO prevent unauthorised access by getters and setters (e.g. primesfile should NEVER be accessed directly
	public:
		Inference		inference;
		INPUTFORMAT 	format;
		OUTPUTFORMAT 	transformat;
		int 			verbosity;
		int 			randomseed;
		int 			nbmodels;
		bool 			printcnfgraph;
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
		POLARITY 		polarity;
		bool 			bumpaggonnotify, bumpidonstart;
		bool			asapaggprop;
		long 			ufsvarintrothreshold;
		bool			decideontseitins;
		bool			subsetminimizeexplanation, currentlevelfirstinexplanation, innogoodfirstinexplanation;
		bool			lazy;

		SolverOption();

		bool 		verifyOptions() const;
		std::string	getPrimesFile() const;
		void print(std::ostream& stream) const;
	};

	enum PrintModel	{PRINT_ALL, PRINT_BEST, PRINT_NONE};
	enum SaveModel	{SAVE_ALL, SAVE_BEST, SAVE_NONE};

	class ModelExpandOptions{
	public:
		PrintModel		printmodels;
		SaveModel		savemodels;
		Inference		search;
		int 			nbmodelstofind;

		ModelExpandOptions():
				printmodels(PRINT_BEST), savemodels(SAVE_NONE), search(MODELEXPAND),
				nbmodelstofind(0){
		}
	};
}

#endif /*EXTERNALUTILS_HPP_*/
