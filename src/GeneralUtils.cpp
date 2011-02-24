/* * Copyright 2007-2011 Katholieke Universiteit Leuven * * Use of this software is governed by the GNU LGPLv3.0 license * * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium */
#include "GeneralUtils.hpp"

#include <cstdlib>
#include <stdio.h>
#include <stdint.h>
#include <tr1/memory>
#include <limits>
#include <ctime>

#include <iostream>
#include <sstream>

#include "external/ExternalUtils.hpp"
#include "satsolver/SATUtils.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

typedef numeric_limits<long> lim;

///////
// Measuring cpu time
///////

//In elapsed seconds, making abstraction of other processes running on the system
double MinisatID::cpuTime(void) {
	return (double)clock() / CLOCKS_PER_SEC;
}

///////
// Weight management
///////

#ifdef GMP
	ostream& Print::operator<<(ostream& output, const Weight& p) {
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

#else //USING FINITE PRECISION WEIGHTS
	string MinisatID::toString(const Weight& w){
		stringstream s;
		s <<w;
		return s.str();
	}
	Weight MinisatID::posInfinity() { return lim::max(); }

	Weight MinisatID::negInfinity() { return lim::min(); }
#endif

///////
// Options for the solvers and their defaults!
///////

#ifndef DATADIR
#warning No data directory defined, assuming it is the build directory
#define DATADIR "."
#endif

SolverOption::SolverOption():
		format(FORMAT_FODOT),
		transformat(TRANS_FODOT),
		verbosity(1),
		nbmodels(1),
		printcnfgraph(false),
		defsem(DEF_WELLF),
		ufs_strategy(breadth_first),
		defn_strategy(always),
		defn_search(include_cs),		checkcyclefreeness(false),
		idclausesaving(0),
		aggclausesaving(2),
		pbsolver(false),		watchesratio(0.75),
		primesfile(""),
		remap(true),
		rand_var_freq(getDefaultRandfreq()),
		var_decay(getDefaultDecay()),
		polarity(getDefaultPolarity()),
		bumpaggonnotify(true),
		bumpidonstart(false),
		subsetminimizeexplanation(false),
		asapaggprop(false),
		ufsvarintrothreshold(500){
	stringstream str;
	str <<DATADIR <<"/P1.TXT";
	primesfile = str.str();
}

bool SolverOption::verifyOptions() const{
	string s(getPrimesFile());
	if(pbsolver && !fileIsReadable(s.c_str())){
		printPrimesFileNotReadable(clog, s);
		return false;
	}	if(var_decay<0.0){		cerr <<"The value for decay should be positive.\n";		return false;	}	if(rand_var_freq<0.0 || rand_var_freq>1.0){		cerr <<"The value for rnd-freq should be between 0 and 1.\n";		return false;	}
	return true;
}

string SolverOption::getPrimesFile() const{
	return primesfile;
}

void SolverOption::print(std::ostream& so) const{
	so << "format: " 			<<format <<"\n";
	so << "verbosity: "			<<verbosity <<"\n";
	so << "nbmodels: " 			<<nbmodels <<"\n";
	so << "printcnfgraph: " 	<<printcnfgraph <<"\n";
	so << "defsem: " 			<<defsem <<"\n";
	so << "ufs_strategy: "		<<ufs_strategy <<"\n";
	so << "defn_strategy: " 	<<defn_strategy <<"\n";
	so << "defn_search: " 		<<defn_search <<"\n";	so << "checking cycles: "	<<checkcyclefreeness <<"\n";
	so << "aggclausesaving: " 	<<aggclausesaving <<"\n";
	so << "pbsolver: " 			<<pbsolver <<"\n";	so << "watchedratio: " 		<<watchesratio <<"\n";
	so << "primesfile: " 		<<getPrimesFile() <<"\n";
	so << "remap: " 			<<remap <<"\n";
	so << "rand_var_freq: " 	<<rand_var_freq <<"\n";
	so << "var_decay: " 		<<var_decay <<"\n";
	so << "polarity: " 			<<polarity <<"\n";
	so << "bumpaggonnotify: " 	<<bumpaggonnotify <<"\n";
	so << "bumpidonstart: " 	<<bumpidonstart <<"\n";
	so << "subsetminimizeexplanation: " <<subsetminimizeexplanation <<"\n";
	so << "asapaggprop: " 		<<asapaggprop <<"\n";
	so << "ufsvarintrothreshold: " <<ufsvarintrothreshold <<"\n";
}
