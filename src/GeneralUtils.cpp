/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "GeneralUtils.hpp"

#include <cstdlib>
#include <cstdio>
#include <cstdint>
#include <limits>
#include <ctime>

#include <iostream>
#include <sstream>

#include "external/ExternalUtils.hpp"
#include "satsolver/SATUtils.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

typedef numeric_limits<int> lim;

// Measuring cpu time

//In elapsed seconds, making abstraction of other processes running on the system
double MinisatID::cpuTime(void) {
	return (double)clock() / CLOCKS_PER_SEC;
}

// Weight management

#ifdef GMP
	ostream& MinisatID::operator<<(ostream& output, const Weight& p) {
		output << p.get_str();
		return output;
	}

	istream& MinisatID::operator>>(istream& input, Weight& obj) {
		long n;
		input >> n;
		obj.w = n;
		return input;
	}

	string MinisatID::toString(const Weight& w){
		return w.get_str();
	}

	Weight MinisatID::abs(const Weight& w) { return w<0?-w:w; }
	Weight MinisatID::posInfinity() { return Weight(true); }
	Weight MinisatID::negInfinity() { return Weight(false); }

	int MinisatID::toInt(const Weight& weight) { return toInt(weight); }

#else //USING FINITE PRECISION WEIGHTS
	string MinisatID::toString(const Weight& w){
		stringstream s;
		s <<w;
		return s.str();
	}
	Weight MinisatID::posInfinity() { return lim::max(); }
	Weight MinisatID::negInfinity() { return lim::min(); }
	int MinisatID::toInt(const Weight& weight) { return weight; }

#endif

// Options for the solvers and their defaults!

#ifndef DATADIR
#warning No data directory defined, assuming it is the build directory
#define DATADIR "."
#endif

SolverOption::SolverOption():
		inference(MODELEXPAND),
		format(FORMAT_FODOT),
		transformat(TRANS_DEFAULT),
		verbosity(1),
		randomseed(91648253),
		nbmodels(1),
		printcnfgraph(false),
		defsem(DEF_WELLF),
		ufs_strategy(breadth_first),
		defn_strategy(always),
		defn_search(include_cs),
		checkcyclefreeness(false),
		idclausesaving(0),
		aggclausesaving(2),
		selectOneFromUFS(false),
		tocnf(false),
		// FIXME watchesratio(0.75),
#warning watches currently disabled
		watchesratio(0),
		useaggheur(false),
		primesfile(""),
		//remap(true),
		rand_var_freq(getDefaultRandfreq()),
		var_decay(getDefaultDecay()),
		polarity(getDefaultPolarity()),
		bumpaggonnotify(true),
		bumpidonstart(false),

		asapaggprop(false),
		ufsvarintrothreshold(500),
		decideontseitins(true),
		subsetminimizeexplanation(false),
		currentlevelfirstinexplanation(true),
		innogoodfirstinexplanation(true),
		lazy(false){
	stringstream str;
	str <<DATADIR <<"/P1.TXT";
	primesfile = str.str();
}

bool SolverOption::verifyOptions() const{
	string s(getPrimesFile());
	if(tocnf && !fileIsReadable(s.c_str())){
		printPrimesFileNotReadable(clog, s);
		return false;
	}
	if(var_decay<0.0){
		cerr <<"The value for decay should be positive.\n";
		return false;
	}
	if(rand_var_freq<0.0 || rand_var_freq>1.0){
		cerr <<"The value for rnd-freq should be between 0 and 1.\n";
		return false;
	}
	return true;
}

string SolverOption::getPrimesFile() const{
	return primesfile;
}

void SolverOption::print(std::ostream& so) const{
	so << "inference: " 		<<inference <<"\n";
	so << "format: " 			<<format <<"\n";
	so << "verbosity: "			<<verbosity <<"\n";
	so << "randomseed: "		<<randomseed <<"\n";
	so << "nbmodels: " 			<<nbmodels <<"\n";
	so << "printcnfgraph: " 	<<printcnfgraph <<"\n";
	so << "defsem: " 			<<defsem <<"\n";
	so << "ufs_strategy: "		<<ufs_strategy <<"\n";
	so << "defn_strategy: " 	<<defn_strategy <<"\n";
	so << "defn_search: " 		<<defn_search <<"\n";
	so << "checking cycles: "	<<checkcyclefreeness <<"\n";
	so << "aggclausesaving: " 	<<aggclausesaving <<"\n";
	so << "tocnf: " 			<<tocnf <<"\n";
	so << "watchedratio: " 		<<watchesratio <<"\n";
	so << "using aggregate heuristic: " <<(useaggheur?"yes":"no") <<"\n";
	so << "primesfile: " 		<<getPrimesFile() <<"\n";
	//so << "remap: " 			<<remap <<"\n";
	so << "rand_var_freq: " 	<<rand_var_freq <<"\n";
	so << "var_decay: " 		<<var_decay <<"\n";
	so << "polarity: " 			<<polarity <<"\n";
	so << "bumpaggonnotify: " 	<<bumpaggonnotify <<"\n";
	so << "bumpidonstart: " 	<<bumpidonstart <<"\n";
	so << "subsetminimizeexplanation: " <<subsetminimizeexplanation <<"\n";
	so << "asapaggprop: " 		<<asapaggprop <<"\n";
	so << "ufsvarintrothreshold: " <<ufsvarintrothreshold <<"\n";
	so << "tseitindecisions: " 	<<decideontseitins <<"\n";
	so << "lazy: " 				<<(lazy?"yes":"no") <<"\n";
}
