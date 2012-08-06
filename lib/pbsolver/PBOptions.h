#pragma once

#include "Int.h"
#include "pbbase/h/SearchMetaData.h"
#include <map>

//=================================================================================================

namespace MiniSatPP {

enum ConvertT {
	ct_Sorters, ct_Adders, ct_BDDs, ct_Mixed, ct_Undef
};
enum Command {
	cmd_Minimize, cmd_FirstSolution, cmd_AllSolutions
};

// if we use sorters (i.e., if ct_Sorters or ct_Mixed are in use),
// how should we determine the base to use?
enum BaseT {
	base_M, base_Forward, base_SOD, base_Carry, base_Comp, base_Rel, base_oddEven, base_Bin
};

enum SortEncding {
	unarySortAddEncoding, oddEvenEncoding, pairwiseSortEncoding
};

struct PBOptions {
	PBOptions();
	// -- output options:
	bool opt_satlive;
	bool opt_ansi;
	char* opt_cnf;
	int opt_verbosity;
	bool opt_try;

	// -- solver options:
	ConvertT opt_convert;
	ConvertT opt_convert_goal;
	bool opt_convert_weak;
	double opt_bdd_thres;
	double opt_sort_thres;
	double opt_goal_bias;
	Int opt_goal;
	Command opt_command;
	bool opt_branch_pbvars;
	int opt_polarity_sug;
	bool opt_validateResoult;

	// -- sorter encoding options
	BaseT opt_base;
	int opt_max_generator;
	bool opt_non_prime;
	bool opt_abstract;
	bool opt_only_base; // web interface: only print optimal base(s), do not solve
	bool opt_skip_sat; // no SAT solving. just say UNSAT
	bool opt_dump; // just dump optimal base problems
	bool opt_natlist; // read list of naturals instead of opb
	bool opt_tare;
	bool opt_use_shortCuts;
	SortEncding opt_sorting_network_encoding;

	// -- require '*' between coeff and var (as MiniSAT+ did in 2005)?
	//    current OPB files do not have this any more.
	bool opt_star_in_input;

	// -- files:
	char* opt_input;
	char* opt_result;
	char* opt_base_result_file;
	char* opt_huge_base_file;

	unsigned int max_number;

	std::vector<SearchMetaData*> baseMetaData;

	std::map<std::map<unsigned int, unsigned int>, unsigned int> baseInputsDumped;
};

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

void reportf(const char* format, ...); // 'printf()' replacer -- will put "c " first at each line if 'opt_satlive' is TRUE.

//=================================================================================================
}
