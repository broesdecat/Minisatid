/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "external/Options.hpp"
#include "external/utils/FileManagement.hpp"
#include "satsolver/SATUtils.hpp"
#include "utils/Print.hpp"

#include <sstream>

using namespace std;
using namespace MinisatID;

void MinisatID::operator&= (SATVAL& orig, SATVAL add){
	orig = (orig==SATVAL::UNSAT || add==SATVAL::UNSAT)?SATVAL::UNSAT:SATVAL::POS_SAT;
}

#ifndef DATADIR
#warning No data directory defined, assuming it is the build directory
#define DATADIR "."
#endif

SolverOption::SolverOption():
		inference(Inference::MODELEXPAND),
		format(InputFormat::FODOT),
		transformat(OutputFormat::DEFAULT),
		verbosity(1),
		randomseed(91648253),
		nbmodels(1),
		defsem(DEF_WELLF),
		ufs_strategy(breadth_first),
		defn_strategy(always),
		defn_search(include_cs),
		checkcyclefreeness(false),
		idclausesaving(0),
		aggclausesaving(2),
		selectOneFromUFS(false),
		tocnf(false),
		splitagg(false),
		//watchesratio(0.751), // Note 0.75 is an often occurring, good ratio to add watches, so a little higher guarantees that for that ratio, watches are introduced
		watchesratio(0), // FIXME Partial watches still bugged! Option also disabled
		primesfile(""),
		rand_var_freq(getDefaultRandfreq()),
		var_decay(getDefaultDecay()),
		polarity(getDefaultPolarity()),
		bumpaggonnotify(true),
		bumpidonstart(false),
		ufsvarintrothreshold(50000),
		subsetminimizeexplanation(false),
		currentlevelfirstinexplanation(true),
		innogoodfirstinexplanation(true),
		lazy(false),
		lazyheur(false),
		watchedrelevance(false),
		expandimmediately(false),
		usegecode(false),
		outputfile(""),
		maxNbOfLearnedClauses(numeric_limits<int>::max()),
		fullmodelcheck(false),
		usesimplifier(false),
		userandomizedrestarts(true),
		flatzinc_a(false){
	stringstream str;
	str <<DATADIR <<"/P1.TXT";
	primesfile = str.str();
}

bool SolverOption::verifyOptions() const{
	string s(getPrimesFile());
	if(tocnf && not fileIsReadable(s.c_str())){
		printPrimesFileNotReadable(clog, s);
		return false;
	}
	if(var_decay<0.0){
		clog <<"The value for decay should be positive.\n";
		return false;
	}
	if(rand_var_freq<0.0 || rand_var_freq>1.0){
		clog <<"The value for rnd-freq should be between 0 and 1.\n";
		return false;
	}
	return true;
}

string SolverOption::getPrimesFile() const{
	return primesfile;
}

void SolverOption::print(std::ostream& so) const{
//	so << "inference: " 		<<inference<<"\n"; TODO
//	so << "format: " 			<<format <<"\n";
	so << "verbosity: "			<<verbosity <<"\n";
	so << "randomseed: "		<<randomseed <<"\n";
	so << "nbmodels: " 			<<nbmodels <<"\n";
	so << "defsem: " 			<<defsem <<"\n";
	so << "ufs_strategy: "		<<ufs_strategy <<"\n";
	so << "defn_strategy: " 	<<defn_strategy <<"\n";
	so << "defn_search: " 		<<defn_search <<"\n";
	so << "double check cycles: "	<<checkcyclefreeness <<"\n";
	so << "aggclausesaving: " 	<<aggclausesaving <<"\n";
	so << "tocnf: " 			<<tocnf <<"\n";
	so << "splitagg: " 			<<splitagg <<"\n";
	so << "watchedratio: " 		<<watchesratio <<"\n";
	so << "primesfile: " 		<<getPrimesFile() <<"\n";
	so << "rand_var_freq: " 	<<rand_var_freq <<"\n";
	so << "var_decay: " 		<<var_decay <<"\n";
//	so << "polarity: " 			<<polarity <<"\n";
	so << "bumpaggonnotify: " 	<<bumpaggonnotify <<"\n";
	so << "bumpidonstart: " 	<<bumpidonstart <<"\n";
	so << "subsetminimizeexplanation: " <<subsetminimizeexplanation <<"\n";
	so << "ufsvarintrothreshold: " <<ufsvarintrothreshold <<"\n";
	so << "lazy: " 				<<(lazy?"yes":"no") <<"\n";
	so << "lazy heuristic: "	<<(lazyheur?"yes":"no") <<"\n";
	so << "watchedrelevance: "	<<(watchedrelevance?"yes":"no") <<"\n";
	so << "expand immediately: "<<(expandimmediately?"yes":"no") <<"\n";
	so << "outputfile: "		<<outputfile <<"\n";
	so << "max number of learned clauses: " <<maxNbOfLearnedClauses <<"\n";
}
