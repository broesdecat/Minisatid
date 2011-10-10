/**************************************************************************************************

Main.C -- (C) Niklas Een, Niklas S�rensson, 2004

Read a DIMACS file and apply the SAT-solver to it.

**************************************************************************************************/


#include <cstdarg>
#include <stdlib.h>
#include <signal.h>
#include <fstream>
#include <vector>
#include <map>
#include <iostream>
#include "MiniSat.h"
#include "PbSolver.h"
#include "PbParser.h"
#include "pbbase/h/SearchMetaData.h"
#include "Hardware.h"
#include "Debug.h"


namespace MiniSatPP {
	
//=================================================================================================
// Command line options:


bool     opt_satlive   = true;
bool     opt_ansi      = true;
char*    opt_cnf       = NULL;
int      opt_verbosity = 1;
bool     opt_try       = false;     // (hidden option -- if set, then "try" to parse, but don't output "s UNKNOWN" if you fail, instead exit with error code 5)

SolverT  opt_solver        = st_MiniSat;
ConvertT opt_convert       = ct_Mixed;
ConvertT opt_convert_goal  = ct_Undef;
bool     opt_convert_weak  = true;
double   opt_bdd_thres     = 3;
double   opt_sort_thres    = 20;
double   opt_goal_bias     = 3;
Int      opt_goal          = Int_MAX;
Command  opt_command       = cmd_Minimize;
bool     opt_branch_pbvars = false;
int      opt_polarity_sug  = 1;

BaseT       opt_base             = base_oddEven;
int         opt_max_generator    = 10000;
bool        opt_non_prime        = false;
bool        opt_only_base        = false; // web interface mode -- v0 is implied
bool        opt_skip_sat         = false; // skip SAT solving, just report UNSAT
bool        opt_dump             = false; // just dump optimal base problems
bool    	opt_natlist          = false; // read list of naturals instead of opb
bool        opt_abstract         = false; // use the abstraction for the base serach algritem (optimalty proven for SOD only!)
bool        opt_tare             = false;
bool 	    opt_use_shortCuts    = false;

bool 		opt_validateResoult  = false;

SortEncding opt_sorting_network_encoding = oddEvenEncoding;
 

bool     opt_star_in_input   = false; // original MiniSAT+ expects "true"

char*    opt_input  		  = NULL;
char*    opt_result 		  = NULL;
char*    opt_base_result_file = NULL;
char*    opt_huge_base_file   = NULL;
const char*    opt_primes_file      = "P1.TXT";

unsigned int    max_number = 0;

int64 numOfDecisions=0;
struct timeval startVal;

std::vector<SearchMetaData*> baseMetaData;
std::map< std::map<unsigned int,unsigned int> , unsigned int> baseInputsDumped;

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

cchar* doc =
    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    "MiniSat++ 0.5, based on MiniSat+ 1.00  -- (C) Niklas Een, Niklas S�rensson, 2005\n"
    "Optimal Base edition -- extensions by\n"
    "Yoav Fekete, Michael Codish, Carsten Fuhs, Peter Schneider-Kamp, 2010\n"
    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    "USAGE: minisat+ <input-file> [<result-file>] [-<option> ...]\n"
    "\n"
    "Solver options:\n"
    "  -M -minisat   Use MiniSat v1.13 as backend (default)\n"
    "  -S -satelite  Use SatELite v1.0 as backend\n"
    "\n"
    "  -ca -adders   Convert PB-constrs to clauses through adders.\n"
    "  -cs -sorters  Convert PB-constrs to clauses through sorters.\n"
    "  -cb -bdds     Convert PB-constrs to clauses through bdds.\n"
    "  -cm -mixed    Convert PB-constrs to clauses by a mix of the above. (default)\n"
    "  -ga/gs/gb/gm  Override conversion for goal function (long name: -goal-xxx).\n"
    "  -w -weak-off  Clausify with equivalences instead of implications.\n"
    "\n"
    "  -bdd-thres=   Threshold for prefering BDDs in mixed mode.        [def: %g]\n"
    "  -sort-thres=  Threshold for prefering sorters. Tried after BDDs. [def: %g]\n"
    "  -goal-bias=   Bias goal function convertion towards sorters.     [def: %g]\n"
    "\n"
    "  -bm           Use minisat+ orignal search algorithm to find base for sorters.\n"
    "  -bf           Use DFS based search algorithm with sum of digits cost function to find base for sorters.\n"
    "  -ba0          Use Brench and bound best first search algorithm with sum of digits cost function to find base for sorters.\n"
    "  -ba1          Use Brench and bound best first search algorithm with sum carry cost function to find base for sorters.\n"
    "  -ba2          Use Brench and bound best first search algorithm with sum aproximate comperators cost function to find base for sorters.\n"
    "  -boe          Use Brench and bound best first search algorithm with sum odd even comperator cost function to find base for sorters.\n"
    "  -br           Use Brench and bound best first search algorithm with relative base comperator to find base for sorters.\n"
    "  -bb           Use the binary base for encoding the sorters.\n"
    "  -max-base=<num>  Use 'num' as max prime factor in base generator. [def: %d]\n"
    "  -non-prime    Allow non-primes in base generators. (default: primes only)\n"
    "  -abs          Allow abstarction of the base search space (optimalty proven for Sum of digits cost function only!).\n"
    "  -nabs         Dont allow abstarction of the base search space (optimalty proven for Sum of digits cost function only!).\n"
    "  -eoe         Use Odd even sorting network encoding.\n"
    "  -esa         Use Sort add sorting network encoding.\n"
    "  -epw         Use Pair wise sorting network encoding.\n"
    "  -scut / -nscut   Enable/diable redundent shortcut clouses to incress sorting network propogation (incress cnf size!).\n"
    "  -tare / -ntare Enable/dsiable tare of the rhs (represented in minmum number of bits in the choosen bits).\n"
    "\n"
    "  -1 -first     Don\'t minimize, just give first solution found\n"
    "  -A -all       Don\'t minimize, give all solutions\n"
    "  -goal=<num>   Set initial goal limit to '<= num'.\n"
    "\n"
    "  -p -pbvars    Restrict decision heuristic of SAT to original PB variables.\n"
    "  -ps{+,-,0}    Polarity suggestion in SAT towards/away from goal (or neutral).\n"
    "\n"
    "  -val validate the corctnes of the found model\n"
    "\n"
    "Input options:\n"
    "  -o -old-star  Require '*' between coefficient and variable. (default: false)\n"
    "  -natlist      Read a list like 3,60,42,77,60; and find an optimal base for it.\n"
    "\n"
    "Output options:\n"
    "  -dump         Just dump the arising Optimal Base Problems\n"
    "  -skip-sat     Use the (incorrect) SAT solver that always says UNSAT.\n"
    "  -only-base    Only compute and print the bases, no solving.\n"
    "  -s -satlive   Turn off SAT competition output.\n"
    "  -a -ansi      Turn off ANSI codes in output.\n"
    "  -v0,-v1,-v2   Set verbosity level (1 default)\n"
    "  -cnf=<file>   Write SAT problem to a file. Trivial UNSAT => no file written.\n"
    "  -base-file=<file>  Append info on the base search for sorters to a file.\n"
    "  -huge-file=<file>  Append here that a base with a number > 17 has been found.\n"
    "  -primes-file=<file> Use to specify the location of primes file. Default=\"P1.TXT\"  .\n"
    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
;

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

bool oneof(cchar* arg, cchar* alternatives)
{
    // Force one leading '-', allow for two:
    if (*arg != '-') return false;
    arg++;
    if (*arg == '-') arg++;

    // Scan alternatives:
    vec<char*>  alts;
    splitString(alternatives, ",", alts);
    for (int i = 0; i < alts.size(); i++){
        if (strcmp(arg, alts[i]) == 0){
            xfreeAll(alts);
            return true;
        }
    }
    xfreeAll(alts);
    return false;
}


void parseOptions(int argc, char** argv)
{
    vec<char*>  args;   // Non-options

    for (int i = 1; i < argc; i++){
        char*   arg = argv[i];
        if (arg[0] == '-'){
          if (oneof(arg,"h,help")) fprintf(stderr, doc, opt_bdd_thres, opt_sort_thres, opt_goal_bias, opt_max_generator), exit(0);

            else if (oneof(arg, "M,minisat" )) opt_solver = st_MiniSat;
            else if (oneof(arg, "S,satelite")) opt_solver = st_SatELite;

            else if (oneof(arg, "ca,adders" )) opt_convert = ct_Adders;
            else if (oneof(arg, "cs,sorters")) opt_convert = ct_Sorters;
            else if (oneof(arg, "cb,bdds"   )) opt_convert = ct_BDDs;
            else if (oneof(arg, "cm,mixed"  )) opt_convert = ct_Mixed;

            else if (oneof(arg, "ga,goal-adders" )) opt_convert_goal = ct_Adders;
            else if (oneof(arg, "gs,goal-sorters")) opt_convert_goal = ct_Sorters;
            else if (oneof(arg, "gb,goal-bdds"   )) opt_convert_goal = ct_BDDs;
            else if (oneof(arg, "gm,goal-mixed"  )) opt_convert_goal = ct_Mixed;

            else if (oneof(arg, "w,weak-off"     )) opt_convert_weak = false;
    
    		else if (oneof(arg, "bm"        )) opt_base      = base_M;
            else if (oneof(arg, "bf"        )) opt_base      = base_Forward;
            else if (oneof(arg, "ba0"       )) opt_base      = base_SOD;
            else if (oneof(arg, "ba1"       )) opt_base      = base_Carry;
            else if (oneof(arg, "ba2"       )) opt_base      = base_Comp;
            else if (oneof(arg, "boe"       )) opt_base      = base_oddEven;
            else if (oneof(arg, "br"        )) opt_base      = base_Rel;
            else if (oneof(arg, "bb"        )) opt_base      = base_Bin;            
            else if (oneof(arg, "non-prime" )) opt_non_prime = true;
            else if (oneof(arg, "only-base" )) opt_only_base = true;
            else if (oneof(arg, "skip-sat"  )) opt_skip_sat  = true;
            else if (oneof(arg, "eoe"       )) opt_sorting_network_encoding  = oddEvenEncoding;
            else if (oneof(arg, "esa"       )) opt_sorting_network_encoding  = unarySortAddEncoding;
            else if (oneof(arg, "epw"       )) opt_sorting_network_encoding  = pairwiseSortEncoding;
            else if (oneof(arg, "abs"))   opt_abstract  = true;
			else if (oneof(arg, "nabs"))  opt_abstract  = false; 
            else if (oneof(arg, "scut"))  opt_use_shortCuts  = true;
            else if (oneof(arg, "nscut")) opt_use_shortCuts  = false;
            else if (oneof(arg, "tare"))  opt_tare   = true;
            else if (oneof(arg, "ntare")) opt_tare   = false;
            
            else if (oneof(arg, "val"))   opt_validateResoult = true;
    
      
            else if (oneof(arg, "dump" )) {
                opt_dump  = true;
                opt_only_base = true; // implied
            }
            else if (oneof(arg, "natlist" )) {
                opt_natlist = true;
                opt_skip_sat = true; // implied
            }
            else if (oneof(arg, "o,old-star")) opt_star_in_input = true;


            //(make nicer later)
            else if (strncmp(arg, "-bdd-thres=" , 11) == 0)    opt_bdd_thres  = atof(arg+11);
            else if (strncmp(arg, "-sort-thres=", 12) == 0)    opt_sort_thres = atof(arg+12);
            else if (strncmp(arg, "-goal-bias=",  11) == 0)    opt_goal_bias  = atof(arg+11);
            else if (strncmp(arg, "-goal="     ,   6) == 0)    opt_goal       = atoi(arg+ 6);  // <<== real bignum parsing here
            else if (strncmp(arg, "-max-base=" ,  10) == 0)    opt_max_generator = atoi(arg+10);
            else if (strncmp(arg, "-cnf="      ,   5) == 0)    opt_cnf        = arg + 5;
            else if (strncmp(arg, "-base-file=",   11) == 0)   opt_base_result_file   = arg + 11;
            else if (strncmp(arg, "-huge-file=",   11) == 0)   opt_huge_base_file   = arg + 11;
            else if (strncmp(arg, "-primes-file=", 13) == 0)   opt_primes_file   = arg + 13;
            //(end)

            else if (oneof(arg, "1,first"   )) opt_command = cmd_FirstSolution;
            else if (oneof(arg, "A,all"     )) opt_command = cmd_AllSolutions;

            else if (oneof(arg, "p,pbvars"  )) opt_branch_pbvars = true;
            else if (oneof(arg, "ps+"       )) opt_polarity_sug = +1;
            else if (oneof(arg, "ps-"       )) opt_polarity_sug = -1;
            else if (oneof(arg, "ps0"       )) opt_polarity_sug =  0;

            else if (oneof(arg, "s,satlive" )) opt_satlive = false;
            else if (oneof(arg, "a,ansi"    )) opt_ansi    = false;
            else if (oneof(arg, "try"       )) opt_try     = true;
            else if (oneof(arg, "v0"        )) opt_verbosity = 0;
            else if (oneof(arg, "v1"        )) opt_verbosity = 1;
            else if (oneof(arg, "v2"        )) opt_verbosity = 2;

            else
                fprintf(stderr, "ERROR! Invalid command line option: %s\n", argv[i]), exit(1);

        }else
            args.push(arg);
    }

    if (args.size() == 0)
      fprintf(stderr, doc, opt_bdd_thres, opt_sort_thres, opt_goal_bias, opt_max_generator), exit(0);
    if (args.size() >= 1)
        opt_input = args[0];
    if (opt_only_base) {
        // special mode for the web interface:
        // only search for bases, not for solutions
        
        // first check whether we support this particular combination
        // of settings
        if (opt_base == base_Forward || opt_base == base_M || opt_base == base_SOD) {
            if (opt_non_prime) {
                reportf("Only primes in base are supported by this base search algorithm!");
                reportf("Exiting ...");
                exit(2);
            }
        }
        // do some overrides to make sure that we only print desired output
        // and that we use sorters for everything
        opt_verbosity = 0;
        opt_convert = ct_Sorters;
        opt_convert_goal = ct_Sorters;
    }
    if (args.size() == 2)
        opt_result = args[1];
    else if (args.size() > 2)
        fprintf(stderr, "ERROR! Too many files specified on commandline.\n"),
        exit(1);
}


//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


void reportf(const char* format, ...)
{
    static bool col0 = true;
    static bool bold = false;
    va_list args;
    va_start(args, format);
    char* text = vnsprintf(format, args);
    va_end(args);

    for(char* p = text; *p != 0; p++){
        if (col0 && opt_satlive)
            putchar('c'), putchar(' ');

        if (*p == '\b'){
            bold = !bold;
            if (opt_ansi)
                putchar(27), putchar('['), putchar(bold?'1':'0'), putchar('m');
            col0 = false;
        }else{
            putchar(*p);
            col0 = (*p == '\n' || *p == '\r');
        }
    }
    fflush(stdout);
}


//=================================================================================================
// Helpers:

double cpuTime1() {
	struct timeval endVal;
    gettimeofday(&endVal, NULL); 
	return ((endVal.tv_sec - startVal.tv_sec)*1000000 + endVal.tv_usec - startVal.tv_usec) / 1000.0;
}

PbSolver*   pb_solver = NULL;   // Made global so that the SIGTERM handler can output best solution found.


void outputResult(const PbSolver& S, bool optimum = true)
{
    if (!opt_satlive) return;

    if (opt_skip_sat) printf("s UNKNOWN\n");
    else if (optimum){
        if (S.best_goalvalue == Int_MAX) printf("s UNSATISFIABLE\n");
        else                             printf("s OPTIMUM FOUND\n");
    }else{
        if (S.best_goalvalue == Int_MAX) printf("s UNKNOWN\n");
        else                             printf("s SATISFIABLE\n");
    }

    if (S.best_goalvalue != Int_MAX){
        printf("v");
        for (int i = 0; i < S.best_model.size(); i++)
            printf(" %s%s", S.best_model[i]?"":"-", S.index2name[i]);
        printf("\n");
    }
    fflush(stdout);
}


static void SIGINT_handler(int signum) {
    reportf("\n");
    reportf("*** INTERRUPTED ***\n");
    SatELite::deleteTmpFiles();
    _Exit(0); }     // (using 'exit()' rather than '_Exit()' sometimes causes the solver to hang (why?))

// yay prototype


SearchMetaData* createDummyData(double cpuT) {
	SearchMetaData* dummyData = new SearchMetaData(0,opt_max_generator,0,0,"");
    dummyData->cost = -1LL;
    dummyData->inputCountCost = -1LL;
    dummyData->basesEvaluated = -1L;
    dummyData->runTime = (long)(cpuT * 1000.0);
    dummyData->insertedToQue = -1L;
    dummyData->nodesExpended = -1L;
    dummyData->maxCoffes = -1;
    dummyData->numOfDifCoffes = -1;
    if (opt_base == base_Forward) dummyData->algType = "DFS_cost_carry";
    else if (opt_base == base_M)  dummyData->algType = "MiniSAT+";
    else if (opt_base == base_SOD) dummyData->algType = "BNB_cost_sumOfDigits";
    else if (opt_base == base_Carry) dummyData->algType = "BNB_cost_carry";
    else if (opt_base == base_Comp) dummyData->algType = "BNB_cost_comp";
    else if (opt_base == base_oddEven) dummyData->algType = "BNB_oddEven_comp";
    else if (opt_base == base_oddEven) dummyData->algType = "BinaryBase";
    else dummyData->algType = "UNKNOWN";
    return dummyData;
}

static void SIGTERM_handler(int signum) {
    reportf("\n");
    reportf("*** TERMINATED ***\n");
    outputResult(*pb_solver, false);
    double cpuT =cpuTime1();
    // start base stuff -- we want to log also timeouts
    if (baseMetaData.size() == 0) {
        // timed out, and we did not even finish base search at least once!
        // => create a dummy entry before printing
        SearchMetaData* dummyData = createDummyData(cpuT);
        baseMetaData.push_back(dummyData);
    }
    if (opt_huge_base_file!=NULL) printHugeOutPut(cpuT,false,true,false);
	else if (opt_base_result_file!=NULL) printBaseOutPut(cpuT,false,true,false);
    // end base stuff
    SatELite::deleteTmpFiles();
    _Exit(pb_solver->best_goalvalue == Int_MAX ? 0 : 10); 
}


void printStats(BasicSolverStats& stats, double cpu_time)
{
    if (opt_skip_sat) reportf("SKIPPED SAT-SOLVING - result may be incorrect\n");
    reportf("restarts              : %"I64_fmt"\n", stats.starts);
    reportf("conflicts             : %-12"I64_fmt"   (%.0f /sec)\n", stats.conflicts   , stats.conflicts   /cpu_time);
    reportf("decisions             : %-12"I64_fmt"   (%.0f /sec)\n", stats.decisions   , stats.decisions   /cpu_time);
    reportf("propagations          : %-12"I64_fmt"   (%.0f /sec)\n", stats.propagations, stats.propagations/cpu_time);
    reportf("inspects              : %-12"I64_fmt"   (%.0f /sec)\n", stats.inspects    , stats.inspects    /cpu_time);
    reportf("CPU time              : %g s\n", cpu_time);
    numOfDecisions = stats.decisions;
}

void printBaseOutPut(double cpuTime,bool isSat,bool timeout,bool exception){
	std::fstream file(opt_base_result_file, std::fstream::out | std::fstream::app);
	if (file.fail()) return;
	file<<"start_run\n";
    double cpuMillis = cpuTime;
    double searchMillis = 0;
    std::vector<SearchMetaData*>::iterator it;
    for ( it=baseMetaData.begin() ; it < baseMetaData.end(); it++ )
    	searchMillis += (*it)->runTime/1000.0;
	double solvingMillis = cpuMillis-searchMillis;
	while(!baseMetaData.empty()) {
		SearchMetaData &md =  (*baseMetaData.back());
	  	file << opt_input <<";"<<md.algType<<";"<<md.primesCutOf<<";";
		int size  = md.base.size();
	  	for(int i=0; i<size;i++) {
	  		file << md.base[i];
	  		if (i!=size-1) file<<",";
	  	}
	  	file <<";"<<md.cost<<";"<<cpuMillis<<";"<<searchMillis<<";"<<solvingMillis<<";"<<md.basesEvaluated<<";";
	  	file << md.nodesExpended<<";"<<md.insertedToQue<<";";
        if (timeout) {file <<"Timeout "<<pb_solver->status <<";";}
        else if (exception)  {file <<"Exception "<<pb_solver->status <<";";}
        else if (isSat) file <<"Yes;";
	  	else file << "No;";
	  	file <<md.maxCoffes<<";"<<md.numOfDifCoffes<<";"<<md.inputCountCost<<";";
	  	if (opt_convert == ct_Adders) file<<"adders;";
        else if (opt_convert == ct_Sorters) file<<"sorters;";
        else if (opt_convert == ct_BDDs) file<<"bdds;";
        else file<<"mixed;";
        if (!opt_non_prime || opt_base==base_Forward || opt_base == base_M || opt_base == base_SOD) file<<"No;"; 
        else file<<"Yes;";
        file<<md.runTime<<";"<<md.fEnvSize<<";"<<pb_solver->formulaSize<<";"<<pb_solver->numOfClouses;
        file<<";"<<md.carryOnlyCost<<";"<<md.compCost<<";";
        size = md.carry.size();
        for(int i=0; i<size;i++) {
	  		file << md.carry[i];
	  		if (i!=size-1) file<<",";
	  	}
	  	file<<";";
	  	size = md.inputs.size();
        for(int i=0; i<size;i++) {
	  		file << md.inputs[i];
	  		if (i!=size-1) file<<",";
	  	}
	  	file<<";"<<md.emptyBaseNOI<<";"<<md.numOfCoffes<<";"<<numOfDecisions;
	  	file<<";"<<opt_abstract<<";"<<opt_tare<<";"<<opt_use_shortCuts<<";"<<opt_convert_weak<<";";
	  	if  (opt_sorting_network_encoding == oddEvenEncoding){
	  		file<<"oddEvenEncoding";
	  	} else if(opt_sorting_network_encoding == pairwiseSortEncoding){
        	file<<"pairwiseSortEncoding";
        } else{
        	file<<"unarySortAddEncoding";
        }
	  	file<<"\n";   
	  	delete baseMetaData.back();
	  	baseMetaData.pop_back();
	}
  	file<<"end_run\n";
    file.flush();
    file.close();

}



void printHugeOutPut(double cpuTime,bool isSat,bool timeout,bool exception){
 	std::fstream file(opt_huge_base_file, std::fstream::out | std::fstream::app);
	if (file.fail()) return;
    bool first = true;
    double cpuMillis = cpuTime;
    double searchMillis = 0;
    std::vector<SearchMetaData*>::iterator it;
    for ( it=baseMetaData.begin() ; it < baseMetaData.end(); it++ )
    	searchMillis += (*it)->runTime/1000.0;
	double solvingMillis = cpuMillis-searchMillis;
	while(!baseMetaData.empty()) {
		SearchMetaData &md =  (*baseMetaData.back());
		int size  = md.base.size();
        bool bigBase = false;
	  	for(int i=0; i<size;i++) {
          if (md.base[i] > 17) {
            bigBase = true;
          }
	  	}
        if (!bigBase) {
          delete baseMetaData.back();
          baseMetaData.pop_back();
          continue;
        }
        if (first) {
          file<<"start_run\n";
          first = false;
        }
	  	file << opt_input <<";"<<md.algType<<";"<<md.primesCutOf<<";";
	  	for(int i=0; i<size;i++) {
	  		file << md.base[i];
	  		if (i!=size-1) file<<",";
	  	}
	  	file <<";"<<md.cost<<";"<<cpuMillis<<";"<<searchMillis<<";"<<solvingMillis<<";"<<md.basesEvaluated<<";";
	  	file << md.nodesExpended<<";"<<md.insertedToQue<<";";
        if (timeout) {file <<"Timeout "<<pb_solver->status <<";";}
        else if (exception)  {file <<"Exception "<<pb_solver->status <<";";}
        else if (isSat) file <<"Yes;";
	  	else file << "No;";
	  	file <<md.maxCoffes<<";"<<md.numOfDifCoffes<<";"<<md.inputCountCost<<";";
	  	if (opt_convert == ct_Adders) file<<"adders;";
        else if (opt_convert == ct_Sorters) file<<"sorters;";
        else if (opt_convert == ct_BDDs) file<<"bdds;";
        else file<<"mixed;";
        if (!opt_non_prime || opt_base==base_Forward || opt_base == base_M || opt_base == base_SOD) file<<"No;"; 
        else file<<"Yes;";
        file<<md.runTime<<";"<<md.fEnvSize<<";"<<pb_solver->formulaSize<<";"<<pb_solver->numOfClouses;
        file<<";"<<md.carryOnlyCost<<";"<<md.compCost<<";";
        size = md.carry.size(); 
        for(int i=0; i<size;i++) {
	  		file << md.carry[i];
	  		if (i!=size-1) file<<",";
	  	}
	  	file<<";";
	  	size = md.inputs.size();
        for(int i=0; i<size;i++) {
	  		file << md.inputs[i];
	  		if (i!=size-1) file<<",";
	  	}
	  	file<<";"<<md.emptyBaseNOI<<";"<<md.numOfCoffes<<";"<<numOfDecisions;
	  	file<<";"<<opt_abstract<<";"<<opt_tare<<";"<<opt_use_shortCuts<<";"<<opt_convert_weak<<";";
	  	if  (opt_sorting_network_encoding == oddEvenEncoding){
	  		file<<"oddEvenEncoding";
	  	} else if(opt_sorting_network_encoding == pairwiseSortEncoding){
        	file<<"pairwiseSortEncoding";
        } else{
        	file<<"unarySortAddEncoding";
        }
	  	file<<"\n"; 
	  	delete baseMetaData.back(); 
	  	baseMetaData.pop_back();
	}
    if (!first) {
      file<<"end_run\n";
    }
    file.flush();
    file.close();
}


PbSolver::solve_Command convert(Command cmd) {
    switch (cmd){
    case cmd_Minimize:      return PbSolver::sc_Minimize;
    case cmd_FirstSolution: return PbSolver::sc_FirstSolution;
    case cmd_AllSolutions:  return PbSolver::sc_AllSolutions;
    default: assert(false); }
}

//=================================================================================================

#define N 10

void test(void)
{
    Formula f = var(0), g = var(N-1);
    for (int i = 1; i < N; i++)
        f = Bin_new(op_Equiv, f, var(i)),
        g = Bin_new(op_Equiv, g, var(N-i-1));

    dump(f); dump(g);

    printf("f= %d\n", index(f));
    printf("g= %d\n", index(g));

    Solver          S(true);
    vec<Formula>    fs;
    fs.push(f ^ g);
    clausify(S, fs);

    S.setVerbosity(1);
    printf(S.solve() ? "SAT\n" : "UNSAT\n");
}

int run(int argc, char** argv) {
	/*DEBUG*/if (argc > 1 && (strcmp(argv[1], "-debug") == 0 || strcmp(argv[1], "--debug") == 0)){ void test(); test(); exit(0); }
    try {
  		gettimeofday(&startVal, NULL);    
	    parseOptions(argc, argv);
	    pb_solver = new PbSolver(); // (must be constructed AFTER parsing commandline options -- constructor uses 'opt_solver' to determinte which SAT solver to use)
	    signal(SIGINT , SIGINT_handler);
	    signal(SIGTERM, SIGTERM_handler);
	    // Set command from 'PBSATISFIABILITYONLY':
	    char* value = getenv("PBSATISFIABILITYONLY");
	    if (value != NULL && atoi(value) == 1)
	        reportf("Setting switch '-first' from environment variable 'PBSATISFIABILITYONLY'.\n"),
	        opt_command = cmd_FirstSolution;
        if (opt_natlist) { // Input is list of integers
            parse_natlist_file(opt_input, *pb_solver);
            opt_convert = ct_Sorters;
            pb_solver->solve(convert(opt_command),true);
            if (opt_base_result_file != NULL) {
                double cpuT = cpuTime1();
                printBaseOutPut(cpuT,false,false,false);
            }
        } else { // Input is opb file
    	    if (opt_verbosity >= 1) reportf("Parsing PB file...\n");
            parse_PB_file(opt_input, *pb_solver);
            pb_solver->solve(convert(opt_command),false);
	
            if (pb_solver->goal == NULL && pb_solver->best_goalvalue != Int_MAX)
                opt_command = cmd_FirstSolution;    // (otherwise output will be wrong)
            if (!pb_solver->okay())
	            opt_command = cmd_Minimize;         // (HACK: Get "UNSATISFIABLE" as output)
	
            // <<== write result to file 'opt_result'
	
            if (opt_command == cmd_Minimize)
                outputResult(*pb_solver);
            else if (opt_command == cmd_FirstSolution)
	            outputResult(*pb_solver, false);
            double cpuT = cpuTime1();
            if (opt_verbosity >= 1) {
                reportf("_______________________________________________________________________________\n\n");
                printStats(pb_solver->stats, cpuT/1000.0);
                reportf("_______________________________________________________________________________\n");
            }
            bool isSat = (pb_solver->best_goalvalue != Int_MAX);
            if (opt_validateResoult) {
            	if (isSat &&!pb_solver->validateResoult()) printf("Error resoult dose not solve the benchmarc!\n");
            	pb_solver->cleanPBC();
            }
            if (opt_huge_base_file!=NULL) printHugeOutPut(cpuT,isSat,false,false);
            else if (opt_base_result_file!=NULL) printBaseOutPut(cpuT,isSat,false,false);
            exit(pb_solver->best_goalvalue == Int_MAX ? 20 : (pb_solver->goal == NULL || opt_command == cmd_FirstSolution) ? 10 : 30);    // (faster than "return", which will invoke the destructor for 'PbSolver')
        }
  }
  catch (Exception_IntOverflow &e) {
		std::cout << "exception caught: " << e.where << std::endl;
		pb_solver->status = e.where;
		reportf("\n");
		double cpuT =cpuTime1();
		if (baseMetaData.size() == 0) {
	        	// exception, and we did not even finish base search at least once!
	        	// => create a dummy entry before printing
	        	SearchMetaData* dummyData = createDummyData(cpuT);
	        	baseMetaData.push_back(dummyData);
	    }
		if (opt_huge_base_file!=NULL)  printHugeOutPut(cpuT,false,false,true); 
		else if (opt_base_result_file!=NULL) printBaseOutPut(cpuT,false,false,true);
		exit(-1);
  }
  return 0;
}

void test1() {
	 opt_convert_weak = false;
	 opt_convert = ct_Sorters;
	 
	 pb_solver = new PbSolver();
	 pb_solver->allocConstrs(8, 4);
	 vec<Lit> ps;
	 vec<Int> Cs;
	 		
	 Int rhs=-1;  //x1 + 2 x2 + 3 x3 + 4 x4 + 5 x5 -20 not x6 <= 4
	 int ineq = 1;
	 ps.push(Lit(2));
	 ps.push(Lit(3));
	 ps.push(Lit(4));
	 ps.push(Lit(5));
	 ps.push(Lit(6));
	 ps.push(Lit(7));
	 Cs.push(1);
	 Cs.push(2);
	 Cs.push(3);
	 Cs.push(4);
	 Cs.push(5);
	 Cs.push(-5);
	 pb_solver->addConstr(ps,Cs,rhs,ineq,false);
	 
/*	 ps.clear();  //x1 + 2 x2 + 3 x3 + 4 x4 + 5 x5 +20 x6 > 4
	 Cs.clear();
	 ps.push(Lit(1));
	 ps.push(Lit(2));
	 ps.push(Lit(3));
	 ps.push(Lit(4));
	 ps.push(Lit(5));
	 ps.push(Lit(6, false));
	 Cs.push(1);
	 Cs.push(2);
	 Cs.push(3);
	 Cs.push(4);
	 Cs.push(5);
	 Cs.push(-20);
	 rhs=4;
	 ineq = -2;
	 pb_solver->addConstr(ps,Cs,rhs,ineq,false);
	 
	 ps.clear(); //x1 + 2 x2 + 3 x3 + 4 x4 + 5 x5 +5 not x7 >= 4
	 Cs.clear();
	 ps.push(Lit(1));
	 ps.push(Lit(2));
	 ps.push(Lit(3));
	 ps.push(Lit(4));
	 ps.push(Lit(5));
	 ps.push(Lit(7,true));
	 Cs.push(1);
	 Cs.push(2);
	 Cs.push(3);
	 Cs.push(4);
	 Cs.push(5);
	 Cs.push(-20);
	 rhs=4;
	 ineq = -1;
	 pb_solver->addConstr(ps,Cs,rhs,ineq,false);
	 
	 ps.clear(); //x1 + 2 x2 + 3 x3 + 4 x4 + 5 x5 -20 x7 < 4
	 Cs.clear();
	 ps.push(Lit(1));
	 ps.push(Lit(2));
	 ps.push(Lit(3));
	 ps.push(Lit(4));
	 ps.push(Lit(5));
	 ps.push(Lit(7, false));
	 Cs.push(1);
	 Cs.push(2);
	 Cs.push(3);
	 Cs.push(4);
	 Cs.push(5);
	 Cs.push(20);
	 rhs=4;
	 ineq = 2;
	 pb_solver->addConstr(ps,Cs,rhs,ineq,false);*/
	// opt_command = cmd_AllSolutions;
	 //pb_solver->solve(convert(opt_command),false);
	 std::vector<std::vector<Lit> > cnf;
	 pb_solver->toCNF(cnf);
	 for (uint i=0;i<cnf.size();i++) {
	 	for(uint j=0;j<cnf[i].size();j++) std::cout<<(sign(cnf[i][j])? "-": "")<< var(cnf[i][j])<<" ";
	 	std::cout<<"\n";
	 }
}

/*void debug1(){
	vec<Formula> fs;
	pb_solver = new PbSolver();
	pb_solver->sat_solver.newVar();
	pb_solver->n_occurs  .push(0);
    pb_solver->n_occurs  .push(0);
    pb_solver->sat_solver.newVar();
	pb_solver->n_occurs  .push(0);
    pb_solver->n_occurs  .push(0);
	fs.push(Lit(0) & Lit(1));
	clausify(pb_solver->sat_solver, fs);
	std::vector<std::vector<Lit> > cnf;
	pb_solver->toCNF(cnf);
	for (int i=0;i<cnf.size();i++) {
	 	for(int j=0;j<cnf[i].size();j++) {
	 		std::cout<<(sign(cnf[i][j])? "-": "")<< var(cnf[i][j])<<" ";
	 	}	
	 	std::cout<<"\n";
	}
}
*/

}


//=================================================================================================


/*int main(int argc, char** argv)
{
	//return MiniSatPP::run(argc,argv);
	MiniSatPP::test1();
	//MiniSatPP::debug1();
	
}*/



