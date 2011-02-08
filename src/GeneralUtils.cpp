//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

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
		defn_search(include_cs),
		idclausesaving(0),
		aggclausesaving(2),
		selectOneFromUFS(false),
		pbsolver(false),
		watchedagg(false),
		primesfile(""),
		remap(true),
		rand_var_freq(getDefaultRandfreq()),
		var_decay(getDefaultDecay()),
		polarity(getDefaultPolarity()),
		bumpaggonnotify(true),
		bumpidonstart(false),
		subsetminimizeexplanation(false),
		asapaggprop(false),
		ufsvarintrothreshold(500),
		aspcomp3type(ASPCOMP3_NOCOMP){

	//Set primesfile location
	char s[300];
	sprintf(s, "%s/P1.TXT", DATADIR);
	primesfile = s;

	//Check primesfile location
	if(!fileIsReadable(s)){
		stringstream str;
		printPrimesFileNotReadable(str, s);
		throw idpexception(str.str());
	}
}

void SolverOption::print(std::ostream& so){
	so << "format: " 			<<format <<"\n";
	so << "verbosity: "			<<verbosity <<"\n";
	so << "nbmodels: " 			<<nbmodels <<"\n";
	so << "printcnfgraph: " 	<<printcnfgraph <<"\n";
	so << "defsem: " 			<<defsem <<"\n";
	so << "ufs_strategy: "		<<ufs_strategy <<"\n";
	so << "defn_strategy: " 	<<defn_strategy <<"\n";
	so << "defn_search: " 		<<defn_search <<"\n";
	so << "aggclausesaving: " 	<<aggclausesaving <<"\n";
	so << "selectOneFromUFS: " 	<<selectOneFromUFS <<"\n";
	so << "pbsolver: " 			<<pbsolver <<"\n";
	so << "watchedagg: " 		<<watchedagg <<"\n";
	so << "primesfile: " 		<<primesfile <<"\n";
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
