/**************************************************************************************************

 Main.C -- (C) Niklas Een, Niklas S�rensson, 2004

 Read a DIMACS file and apply the SAT-solver to it.

 **************************************************************************************************/

#include <cstdarg>
#include <unistd.h>
#include <signal.h>
#include <fstream>
#include <vector>
#include <map>
#include <iostream>
#include "MiniSat.h"
#include "PbSolver.h"
#include "pbbase/h/SearchMetaData.h"
#include "Hardware.h"

namespace MiniSatPP {

//=================================================================================================
// Command line options:

PBOptions::PBOptions()
		: opt_satlive(true), opt_ansi(true), opt_cnf(NULL), opt_verbosity(1),
		  	  opt_try(false),   // (hidden option -- if set, then "try" to parse, but don't output "s UNKNOWN" if you fail, instead exit with error code 5)
			opt_convert(ct_Mixed), opt_convert_goal(ct_Undef), opt_convert_weak(true), opt_bdd_thres(3), opt_sort_thres(20), opt_goal_bias(3),
			opt_goal(Int_MAX), opt_command(cmd_Minimize), opt_branch_pbvars(false), opt_polarity_sug(1),
			opt_base(base_oddEven),
			opt_max_generator(10000), opt_non_prime(false), opt_only_base(false), // web interface mode -- v0 is implied
			opt_skip_sat(false), // skip SAT solving, just report UNSAT
			opt_dump(false), // just dump optimal base problems
			opt_natlist(false), // read list of naturals instead of opb
			opt_abstract(true), // use the abstraction for the base serach algritem (optimalty proven for SOD only!)
			opt_tare(false), opt_use_shortCuts(false),
			opt_validateResoult(false),
			opt_sorting_network_encoding(oddEvenEncoding),
			opt_star_in_input(false), // original MiniSAT+ expects "true"
			opt_input(NULL), opt_result(NULL), opt_base_result_file(NULL), opt_huge_base_file(NULL),
			max_number(0) {
}

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

//    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
//    "MiniSat++ 0.5, based on MiniSat+ 1.00  -- (C) Niklas Een, Niklas S�rensson, 2005\n"
//    "Optimal Base edition -- extensions by\n"
//    "Yoav Fekete, Michael Codish, Carsten Fuhs, Peter Schneider-Kamp, 2010\n"
//    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
//    "USAGE: minisat+ <input-file> [<result-file>] [-<option> ...]\n"
//    "\n"
//    "Solver options:\n"
//    "  -M -minisat   Use MiniSat v1.13 as backend (default)\n"
//    "  -S -satelite  Use SatELite v1.0 as backend\n"
//    "\n"
//    "  -ca -adders   Convert PB-constrs to clauses through adders.\n"
//    "  -cs -sorters  Convert PB-constrs to clauses through sorters.\n"
//    "  -cb -bdds     Convert PB-constrs to clauses through bdds.\n"
//    "  -cm -mixed    Convert PB-constrs to clauses by a mix of the above. (default)\n"
//    "  -ga/gs/gb/gm  Override conversion for goal function (long name: -goal-xxx).\n"
//    "  -w -weak-off  Clausify with equivalences instead of implications.\n"
//    "\n"
//    "  -bdd-thres=   Threshold for prefering BDDs in mixed mode.        [def: %g]\n"
//    "  -sort-thres=  Threshold for prefering sorters. Tried after BDDs. [def: %g]\n"
//    "  -goal-bias=   Bias goal function convertion towards sorters.     [def: %g]\n"
//    "\n"
//    "  -bm           Use minisat+ orignal search algorithm to find base for sorters.\n"
//    "  -bf           Use DFS based search algorithm with sum of digits cost function to find base for sorters.\n"
//    "  -ba0          Use Brench and bound best first search algorithm with sum of digits cost function to find base for sorters.\n"
//    "  -ba1          Use Brench and bound best first search algorithm with sum carry cost function to find base for sorters.\n"
//    "  -ba2          Use Brench and bound best first search algorithm with sum aproximate comperators cost function to find base for sorters.\n"
//    "  -boe          Use Brench and bound best first search algorithm with sum odd even comperator cost function to find base for sorters.\n"
//    "  -br           Use Brench and bound best first search algorithm with relative base comperator to find base for sorters.\n"
//    "  -bb           Use the binary base for encoding the sorters.\n"
//    "  -max-base=<num>  Use 'num' as max prime factor in base generator. [def: %d]\n"
//    "  -non-prime    Allow non-primes in base generators. (default: primes only)\n"
//    "  -abs          Allow abstarction of the base search space (optimalty proven for Sum of digits cost function only!).\n"
//    "  -nabs         Dont allow abstarction of the base search space (optimalty proven for Sum of digits cost function only!).\n"
//    "  -eoe         Use Odd even sorting network encoding.\n"
//    "  -esa         Use Sort add sorting network encoding.\n"
//    "  -epw         Use Pair wise sorting network encoding.\n"
//    "  -scut / -nscut   Enable/diable redundent shortcut clouses to incress sorting network propogation (incress cnf size!).\n"
//    "  -tare / -ntare Enable/dsiable tare of the rhs (represented in minmum number of bits in the choosen bits).\n"
//    "\n"
//    "  -1 -first     Don\'t minimize, just give first solution found\n"
//    "  -A -all       Don\'t minimize, give all solutions\n"
//    "  -goal=<num>   Set initial goal limit to '<= num'.\n"
//    "\n"
//    "  -p -pbvars    Restrict decision heuristic of SAT to original PB variables.\n"
//    "  -ps{+,-,0}    Polarity suggestion in SAT towards/away from goal (or neutral).\n"
//    "\n"
//    "  -val validate the corctnes of the found model\n"
//    "\n"
//    "Input options:\n"
//    "  -o -old-star  Require '*' between coefficient and variable. (default: false)\n"
//    "  -natlist      Read a list like 3,60,42,77,60; and find an optimal base for it.\n"
//    "\n"
//    "Output options:\n"
//    "  -dump         Just dump the arising Optimal Base Problems\n"
//    "  -skip-sat     Use the (incorrect) SAT solver that always says UNSAT.\n"
//    "  -only-base    Only compute and print the bases, no solving.\n"
//    "  -s -satlive   Turn off SAT competition output.\n"
//    "  -a -ansi      Turn off ANSI codes in output.\n"
//    "  -v0,-v1,-v2   Set verbosity level (1 default)\n"
//    "  -cnf=<file>   Write SAT problem to a file. Trivial UNSAT => no file written.\n"
//    "  -base-file=<file>  Append info on the base search for sorters to a file.\n"
//    "  -huge-file=<file>  Append here that a base with a number > 17 has been found.\n"
//    "  -primes-file=<file> Use to specify the location of primes file. Default=\"P1.TXT\"  .\n"
//    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

void reportf(const char* format, ...) {
	static bool col0 = true;
	static bool bold = false;
	va_list args;
	va_start(args, format);
	char* text = vnsprintf(format, args);
	va_end(args);

	for (char* p = text; *p != 0; p++) {
		if (*p == '\b') {
			bold = !bold;
			col0 = false;
		} else {
			putchar(*p);
			col0 = (*p == '\n' || *p == '\r');
		}
	}
	fflush(stdout);
}

}

//=================================================================================================
