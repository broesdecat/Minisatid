//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#include <cstdlib>
#include <stdio.h>
#include <stdint.h>
#include <tr1/memory>
#include <limits>
#include <ctime>

#include <iostream>

#include "external/ExternalUtils.hpp"
#include "satsolver/SATUtils.hpp"

using namespace std;
using namespace MinisatID;

typedef numeric_limits<long> lim;

///////
// Measuring cpu time and memory management
///////

//In elapsed seconds, making abstraction of other processes running on the system
double MinisatID::cpuTime(void) {
	return (double)clock() / CLOCKS_PER_SEC;
}

#if defined(__linux__)
	static inline int memReadStat(int field){
		int read;
		char    name[256];
		pid_t pid = getpid();
		sprintf(name, "/proc/%d/statm", pid);
		FILE*   in = fopen(name, "rb");
		if (in == NULL) return 0;
		int     value;
		for (; field >= 0; field--){
			read = fscanf(in, "%d", &value);
			if(read==EOF){ break; }
		}
		fclose(in);
		return value;
	}
	static inline uint64_t memUsed() { return (uint64_t)memReadStat(0) * (uint64_t)getpagesize(); }
#elif defined(__FreeBSD__)
	static inline uint64_t memUsed(void) {
		struct rusage ru;
		getrusage(RUSAGE_SELF, &ru);
		return ru.ru_maxrss*1024;
	}
#else
	static inline uint64_t memUsed() { return 0; }
#endif

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
Weight MinisatID::abs(const Weight& w) { return w<0?-w:w; }
Weight MinisatID::posInfinity() { return Weight(true); }
Weight MinisatID::negInfinity() { return Weight(false); }
#else
Weight MinisatID::posInfinity() { return lim::max(); }
Weight MinisatID::negInfinity() { return lim::min(); }
#endif

#ifdef GMP
	string MinisatID::toString(const Weight& w){
		return w.get_str();
	}
#else //INT_WEIGHT
	string MinisatID::toString(const Weight& w){
		char s[15];
		sprintf(s, "%d", w);
		return s;
	}
#endif

///////
// Options for the solvers and their defaults!
///////

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
	ufsvarintrothreshold(500){}

void SolverOption::print(){
	cerr << "format: " <<format <<endl;
	cerr << "verbosity: " <<verbosity <<endl;
	cerr << "nbmodels: " <<nbmodels <<endl;
	cerr << "printcnfgraph: " <<printcnfgraph <<endl;
	cerr << "defsem: " <<defsem <<endl;
	cerr << "ufs_strategy: " <<ufs_strategy <<endl;
	cerr << "defn_strategy: " <<defn_strategy <<endl;
	cerr << "defn_search: " <<defn_search <<endl;
	cerr << "aggclausesaving: " <<aggclausesaving <<endl;
	cerr << "selectOneFromUFS: " <<selectOneFromUFS <<endl;
	cerr << "pbsolver: " <<pbsolver <<endl;
	cerr << "watchedagg: " <<watchedagg <<endl;
	cerr << "primesfile: " <<primesfile <<endl;
	cerr << "remap: " <<remap <<endl;
	cerr << "rand_var_freq: " <<rand_var_freq <<endl;
	cerr << "var_decay: " <<var_decay <<endl;
	cerr << "polarity: " <<polarity <<endl;
	cerr << "bumpaggonnotify: " <<bumpaggonnotify <<endl;
	cerr << "bumpidonstart: " <<bumpidonstart <<endl;
	cerr << "subsetminimizeexplanation: " <<subsetminimizeexplanation <<endl;
	cerr << "asapaggprop: " <<asapaggprop <<endl;
	cerr << "ufsvarintrothreshold: " <<ufsvarintrothreshold <<endl;
}
