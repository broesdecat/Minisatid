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

#include "solvers/external/ExternalUtils.hpp"

#ifdef GMPWEIGHT
	string printWeight(const Weight& w){
		return w.get_str();
	}
#else
	#ifdef BIGINTWEIGHT
		string printWeight(const Weight& w){
			return bigIntegerToString(w);
		}
	#else //INT_WEIGHT
		string printWeight(const Weight& w){
			char s[15];
			sprintf(s, "%d", w);
			return s;
		}
	#endif
#endif

/*IntOption::IntOption(ECNF_mode& mode, string naam, int min, int max, string description):
		naam(naam), min(min), max(max), description(description){
	mode.addVar(*this, naam);
}

void ECNF_mode::addVar(const IntOption& opt, string naam){
	mapping.insert(pair<string, IntOption>(naam, opt));
	variabelen.push_back(opt);
}*/

void ECNF_mode::printUsage(){
	reportf("Usage: program [options] <input-file> <result-output-file>\n\n  where input may is in ECNF, LParse, PB or MECNF.\n\n");
	reportf("Options:\n\n");
	/*for(int i=0; i<variabelen.size(); i++){
		variabelen[i].printHelp();
	}*/
	reportf("   --defsearch        Unfounded set search frequency: \"always\", \"adaptive\" or \"lazy\".\n");
	reportf("   --defstrat         Unfounded set search strategy: \"breadth_first\" or \"depth_first\".\n");
	reportf("   --defsem           Semantics of all definitions: \"stable\" or \"wellfounded\".\n");
	reportf("   --n<I>             The number of models <I> to search for.\n");
	reportf("   --verbosity=<I>    The level of output <I> to generate.\n");
	reportf("   --rnd-freq=<D>     <D> is a double \\in [0..1].\n");
	reportf("   --decay=<D>        <D> is a double \\in [0..1].\n");
	reportf("   --polarity-mode    Default polarity choice of variables: \"true\", \"false\" or \"rnd\".\n");
	reportf("   --defsearch        Unfounded set search frequency: \"always\", \"adaptive\" or \"lazy\".\n");
	reportf("   --lparse=<B>       \"yes\" if the input is in ASP lparse format.\n");
	reportf("   --pb=<B>           \"yes\" if the input is in PB format.\n");
	reportf("   --idclausesaving=<I> 0=add on propagation, 1=save on propagation.\n");
	reportf("   --aggclausesaving=<I> 0=add on propagation, 1=save on propagation, 2 = dont save.\n");
	reportf("   --remap=<B>        \"yes\" if all literals should be remapped to remove gaps in the grouding.\n");
	reportf("   --pw=<B>           \"yes\" if watched aggregate structures should be used.\n");
	reportf("   --randomize=<B>    \"yes\" if the SAT-solver random seed should be random.\n");
	reportf("   --disableheur=<B>  \"yes\" if the SAT-solver's heuristic should be disabled.\n");
	reportf("\n");
}

void ECNF_mode::parseCommandline(int& argc, char** argv){
    /*TODO int         i, j;
    const char* value;
    for (i = j = 0; i < argc; i++){
    	//read --, otherwise inputfile
    	//read until =
    	//read option (done by Option)
    	if(){

    	}*/
}
