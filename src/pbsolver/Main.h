#ifndef Main_h
#define Main_h

#include "Int.h"
#include "pbbase/h/SearchMetaData.h"
#include <vector>
#include <map>

//=================================================================================================

namespace MiniSatPP {

enum SolverT  { st_MiniSat, st_SatELite };
enum ConvertT { ct_Sorters, ct_Adders, ct_BDDs, ct_Mixed, ct_Undef };
enum Command  { cmd_Minimize, cmd_FirstSolution, cmd_AllSolutions };


// if we use sorters (i.e., if ct_Sorters or ct_Mixed are in use),
// how should we determine the base to use?
enum BaseT { base_M,base_Forward, base_SOD, base_Carry, base_Comp, base_Rel,base_oddEven, base_Bin };

enum SortEncding { unarySortAddEncoding, oddEvenEncoding, pairwiseSortEncoding};


// -- output options:
extern bool     opt_satlive;
extern bool     opt_ansi;
extern char*    opt_cnf;
extern int      opt_verbosity;
extern bool     opt_try;

// -- solver options:
extern SolverT  opt_solver;
extern ConvertT opt_convert;
extern ConvertT opt_convert_goal;
extern bool     opt_convert_weak;
extern double   opt_bdd_thres;
extern double   opt_sort_thres;
extern double   opt_goal_bias;
extern Int      opt_goal;
extern Command  opt_command;
extern bool     opt_branch_pbvars;
extern int      opt_polarity_sug;
extern bool     opt_validateResoult;

// -- sorter encoding options
extern BaseT opt_base;
extern int   opt_max_generator;
extern bool  opt_non_prime;
extern bool  opt_abstract; 
extern bool  opt_only_base; // web interface: only print optimal base(s), do not solve
extern bool  opt_skip_sat;  // no SAT solving. just say UNSAT
extern bool  opt_dump; // just dump optimal base problems
extern bool  opt_natlist; // read list of naturals instead of opb
extern bool  opt_tare;
extern bool  opt_use_shortCuts;
extern SortEncding   opt_sorting_network_encoding;


// -- require '*' between coeff and var (as MiniSAT+ did in 2005)?
//    current OPB files do not have this any more.
extern bool  opt_star_in_input;

// -- files:
extern char*    opt_input;
extern char*    opt_result;
extern char*    opt_base_result_file;
extern char*    opt_huge_base_file;
extern const char*    opt_primes_file;

extern unsigned int    max_number;

extern std::vector<SearchMetaData*> baseMetaData; 

extern std::map<
                 std::map<unsigned int, unsigned int> ,
                 unsigned int
               > baseInputsDumped;


//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

void reportf(const char* format, ...);      // 'printf()' replacer -- will put "c " first at each line if 'opt_satlive' is TRUE.

void printHugeOutPut(double cpuTime,bool isSat,bool timeout,bool exception);
void printBaseOutPut(double cpuTime,bool isSat,bool timeout,bool exception);

SearchMetaData* createDummyData(double cpuT);

//=================================================================================================
}


#endif
