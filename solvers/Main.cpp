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

/************************************************************************************
 Copyright (c) 2006-2009, Maarten Mariën

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/
/****************************************************************************************[Main.c]
 MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include <ctime>
#include <cstring>
#include <stdint.h>
#include <cerrno>
#include <iostream>
#include <fstream>
#include <signal.h>
#include <tr1/memory>
#include <argp.h>
#include <sstream>

#include "solvers/external/ExternalInterface.hpp"
#include "solvers/Unittests.hpp"
#include "solvers/parser/Lparseread.hpp"
#include "solvers/parser/PBread.hpp"

#if defined(__linux__)
#include <fpu_control.h>
#endif

using namespace std;
using namespace std::tr1;
using namespace MinisatID;

ECNF_mode modes;

namespace MinisatID {
class WrappedLogicSolver;
typedef shared_ptr<WrappedLogicSolver> pData;
}

extern char * yytext;
extern int lineNo;
extern int charPos;
extern pData getData();

//extern FILE*	ecnfin;
//extern int	ecnfparse	();
extern FILE* yyin;
extern int yyparse();
extern void yydestroy();
extern void yyinit();
extern bool unsatfound;

const char* hasPrefix(const char* str, const char* prefix);
void parseCommandline(int& argc, char** argv);
pData parse();

void printStats();
static void SIGINT_handler(int signum);
void printUsage(char** argv);

void noMoreMem() {
	//Tries to reduce the memory of the solver by reducing the number of learned clauses
	//This keeps being called until enough memory is free or no more learned clauses can be deleted (causing abort).
	throw idpexception("The solver ran out of memory.\n");
	bool reducedmem = false;
	//	pSolver s = wps.lock();
	//	if(s.get()!=NULL){
	//		int before = s->getNbOfLearnts();
	//		if(before > 0){
	//			s->reduceDB();
	//			int after = s->getNbOfLearnts();
	//			if(after<before){
	//				reducedmem = true;
	//			}
	//		}
	//	}
	//
	if (!reducedmem) {
		throw idpexception("The solver ran out of memory.\n");
	}
}

void printVersion() {
	reportf("MinisatID version 2.0.20\n");
	reportf("Courtesy of the KRR group at K.U. Leuven, Belgium, more info available on \"http://dtai.cs.kuleuven.be/krr\".\n");
	reportf("MinisatID is a model expansion system for propositional logic extended with aggregates "
			"and inductive definitions. Also lparse and opb languages are supported.\n");
}

void printUsage() {
	reportf("Usage: program [options] <input-file> <result-output-file>\n\n  where input may is in ECNF, LParse, PB or MECNF.\n\n");
	reportf("Options:\n\n");
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
	reportf("   --aggclausesaving=<I> 0=add on propagation, 1=save on propagation, 2 = don't save.\n");
	reportf("   --remap=<B>        \"yes\" if all literals should be remapped to remove gaps in the grounding.\n");
	reportf("   --pw=<B>           \"yes\" if watched aggregate structures should be used.\n");
	reportf("   --randomize=<B>    \"yes\" if the SAT-solver random seed should be random.\n");
	reportf("   --disableheur=<B>  \"yes\" if the SAT-solver's heuristic should be disabled.\n");
	reportf("\n");
}

const char *argp_program_version = "minisatid 2.1.20";
const char *argp_program_bug_address = "<krr@cs.kuleuven.be>";

/* Program documentation. */
static char doc[] =
		"Courtesy of the KRR group at K.U. Leuven, Belgium, more info available on \"http://dtai.cs.kuleuven.be/krr\".\n"
			"MinisatID is a model expansion system for propositional logic extended with aggregates "
			"and inductive definitions. Also lparse and opb languages are supported.\n";

/* A description of the arguments we accept. */
static char args_doc[] = "input-file output-file";

/* The options we understand. */
static struct argp_option options[] = {
		{"models"		, 'n', "MOD", 0,	"The number of models MOD to search for"},
		{"verbosity"	, 1, "VERB", 0,		"The level of output VERB to generate"},
		{"rnd-freq"		, 2, "FREQ", 0,		"The frequency FREQ (in [0..1]) with which to make a random choice"},
		{"decay"		, 3, "DEC", 0,		"The amount of decay DEC (in [0..1]) used by the SAT-solver"},
		{"polarity-mode", 4, "POL", 0,		"POL={\"true\", \"false\", \"rnd\"}: sets the default polarity choice of variables"},
		{"format"		, 'f', "FORMAT",  0, "FORMAT={\"fodot\", \"lparse\", \"opb\"}: treat input propositional FO(.), as lparse ground format or as pseudo-boolean input"},
		{"idclausesaving", 5, "ID", 0,		"INT={0,1}: 0=add clause on propagation, 1=save clause on propagation"},
		{"aggclausesaving", 6, "INT", 0,	"INT={0,1,2}: 0=add clause on propagation, 1=save clause on propagation, 2=save minimal reason"},
		{"remap"		, 'r', "BOOL", 0,	"BOOL={\"yes\",\"no\"}: remap literals from the input structure to a gap-less internal format"},
		{"watchedaggr"	, 'w', "BOOL", 0,	"BOOL={\"yes\",\"no\"}: use watched-literal datastructures to handle aggregate propagation"},
		{"output"		, 'o', "FILE", 0,	"The outputfile to use to write out models and results"},
		{"randomize"	, 7, "BOOL", 0,		"BOOL={\"yes\",\"no\"}: randomly generate the SAT-solver random seed"},
//		{"disableheur"	, 8, "BOOL", 0,		"BOOL={\"yes\",\"no\"}: disable the SAT-solver's heuristic"},
//		{"defstrat "	, 9, "STRAT", 0,	"STRAT={\"breadth_first\", \"depth_first\"}: sets the unfounded-set search-strategy"},
		{"defsearch"	, 10, "SEARCH", 0,	"SEARCH={\"always\", \"adaptive\", \"lazy\"}: sets the unfounded-set search-frequency"},
		{"defsem"		, 11, "SEM", 0,		"SEM={\"stable\", \"wellfounded\"}: uses the chosen semantics to handle inductive definitions"},
		{ 0 } }; //Required end tuple

/* Parse a single option. */
static error_t parse_opt(int key, char *arg, struct argp_state *state) {
	/* Get the input argument from argp_parse, which we know is a pointer to our arguments structure. */
	struct ECNF_mode *args = static_cast<ECNF_mode*>(state->input);
	assert(args!=NULL);

	reportf("Key: %d, argument: %s\n", key, arg);
	switch (key) {
		case 1: // verbosity
			if((stringstream(arg) >> modes.verbosity).fail()){
				reportf("Illegal verbosity value %s\n", arg); argp_usage(state);
			}
			break;
		case 2: // rnd-freq
			if((stringstream(arg) >> modes.random_var_freq).fail() || modes.var_decay>1.0 || modes.var_decay<0.0){
				reportf("Illegal rnd-freq value %s\n", arg); argp_usage(state);
			}
			break;
		case 3: // decay
			if((stringstream(arg) >> modes.var_decay).fail() || modes.var_decay>1.0 || modes.var_decay<0.0){
				reportf("Illegal decay value %s\n", arg); argp_usage(state);
			}
			break;
		case 4: // polarity
			if(strcmp(arg, "true")){
				modes.polarity_mode = polarity_true;
			}else if(strcmp(arg, "false")){
				modes.polarity_mode = polarity_false;
			}else if(strcmp(arg, "rnd")){
				modes.polarity_mode = polarity_rnd;
			}else{
				reportf("Illegal polarity value %s\n", arg); argp_usage(state);
			}
			break;
		case 5: // id clausesaving
			if((stringstream(arg) >> modes.idclausesaving).fail() || modes.aggclausesaving>1 || modes.aggclausesaving<0){
				reportf("Illegal idclausesaving value %s\n", arg); argp_usage(state);
			}
			break;
		case 6: // agg clause saving
			if((stringstream(arg) >> modes.aggclausesaving).fail() || modes.aggclausesaving>2 || modes.aggclausesaving<0){
				reportf("Illegal aggclausesaving value %s\n", arg); argp_usage(state);
			}
			break;
		case 7: // randomize: yes/no
			if(strcmp(arg, "no")){
				modes.randomize = false;
			}else if(strcmp(arg, "yes")){
				modes.randomize = true;
			}else{
				reportf("Illegal randomize value %s\n", arg); argp_usage(state);
			}
			break;
		case 8: // disableheur
			throw idpexception("Option not implemented!\n");
			break;
		case 9: // defstrat: breadth_first/depth_first
			throw idpexception("Option not implemented!\n");
			/*if(strcmp(arg, "breadth_first")){
				modes.ufs_strategy = breadth_first;
			}else if(strcmp(arg, "depth_first")){
				modes.ufs_strategy = depth_first;
			}else{
				reportf("Illegal defstrat value %s\n", arg); argp_usage(state);
			}*/
			break;
		case 10: // defsearch: always/adaptive/lazy
			if(strcmp(arg, "always")){
				modes.defn_strategy = always;
			}else if(strcmp(arg, "adaptive")){
				modes.defn_strategy = adaptive;
			}else if(strcmp(arg, "lazy")){
				modes.defn_strategy = lazy;
			}else{
				reportf("Illegal defsearch value %s\n", arg); argp_usage(state);
			}
			break;
		case 11: // defsem: stable/wellfounded
			if(strcmp(arg, "stable")){
				modes.sem = STABLE;
			}else if(strcmp(arg, "wellfounded")){
				modes.sem = WELLF;
			}else{
				reportf("Illegal defsem value %s\n", arg); argp_usage(state);
			}
			break;
		case 'n': // models
			if((stringstream(arg) >> modes.nbmodels).fail() || modes.nbmodels<0){
				reportf("Illegal nbmodels value %s\n", arg); argp_usage(state);
			}
			break;
		case 'f':
			if(strcmp(arg, "fodot")){
				modes.lparse = false; modes.pb = false;
			}else if(strcmp(arg, "lparse")){
				modes.lparse = true; modes.pb = false;
			}else if(strcmp(arg, "opb")){
				modes.lparse = false; modes.pb = true;
			}else{
				reportf("Illegal format value %s\n", arg); argp_usage(state);
			}
			break;
		case 'r': // remap: yes/no
			if(strcmp(arg, "no")){
				modes.remap = false;
			}else if(strcmp(arg, "yes")){
				modes.remap = true;
			}else{
				reportf("Illegal remap value %s\n", arg); argp_usage(state);
			}
			break;
		case 'o': // outputfile
			MinisatID::setOutputFileUrl(arg);
			break;
		case 'w': // watched agg: yes/no
			if(strcmp(arg, "no")){
				modes.pw = false;
			}else if(strcmp(arg, "yes")){
				modes.pw = true;
			}else{
				reportf("Illegal watchedaggr value %s\n", arg); argp_usage(state);
			}
			break;
		case ARGP_KEY_ARG:
			if(state->arg_num >2){ // Too many arguments.
				reportf("Too many extra arguments\n");
				argp_usage(state);
			}
			if(state->arg_num == 0){
				reportf("Set inputfile url\n");
				MinisatID::setInputFileUrl(arg);
			}else if(state->arg_num == 1){
				reportf("Set outputfile url\n");
				MinisatID::setOutputFileUrl(arg);
			}
			break;
		case ARGP_KEY_END: // Piping is allowed, so don't really need any files
			break;
		default:
			return ARGP_ERR_UNKNOWN;
	}
	return 0;
}

/* Our argp parser. */
static struct argp argp = { options, parse_opt, args_doc, doc };


///////
// Option datastructure
///////

int main(int argc, char** argv) {
	//Setting system precision and signal handlers
#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw);
	newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
	_FPU_SETCW(newcw);
	if (modes.verbosity >= 1)
		reportf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
	signal(SIGINT, SIGINT_handler);
#if defined(__linux__)
	signal(SIGHUP, SIGINT_handler);
#endif
	//set memory handler
	std::set_new_handler(noMoreMem);

	//set start time
	double cpu_time = cpuTime();

	//parse command-line options
	argp_parse(&argp, argc, argv, 0, 0, &modes);

	if(modes.verbosity >= 1){
		reportf("============================[ Problem Statistics ]=============================\n");
		reportf("| Parsing input                                                               |\n");
	}

	pData d;
	int returnvalue = 1;
	try { // Start catching IDP exceptions
		// Unittest injection by   pData d = unittestx(modes);

		//Parse input
		if (modes.lparse) {
			modes.aggr = true;
			modes.def = true;
			WrappedPCSolver* p = new WrappedPCSolver(modes);
			d = shared_ptr<WrappedLogicSolver> (p);
			Read* r = new Read(p);
			std::filebuf buf;
			buf.open(MinisatID::getInputFileUrl(), std::ios::in);
			std::istream is(&buf);
			r->read(is);
			buf.close();
			delete r;
		} else if (modes.pb) { //PB
			modes.aggr = true;
			modes.mnmz = true;
			WrappedPCSolver* p = new WrappedPCSolver(modes);
			d = shared_ptr<WrappedLogicSolver> (p);
			PBRead* parser = new PBRead(p, MinisatID::getInputFileUrl());
			parser->autoLin();
			parser->parse();
			delete parser;
		} else {
			yyin = MinisatID::getInputFile();
			d = parse();
		}

		MinisatID::closeInput();

		assert(d.get()!=NULL);

		if (modes.verbosity >= 1) {
			reportf("| Parsing input finished                                                      |\n");
			reportf("| Datastructure initialization                                                |\n");
		}

		//Initialize datastructures
		bool unsat = !d->finishParsing();

		if (modes.verbosity >= 1) {
			reportf("| Datastructure initialization finished                                       |\n");
			double parse_time = cpuTime() - cpu_time;
			reportf("| Total parsing time              : %7.2f s                                 |\n", parse_time);
			if (unsat) {
				reportf("===============================================================================\n"
						"Unsatisfiable found by parsing\n");
			}
		}

		//Simplify
		if(!unsat){
			unsat = !d->simplify();
			if(unsat){
				if (modes.verbosity >= 1) {
					reportf("===============================================================================\n"
							"Unsatisfiable found by unit propagation\n");
				}
			}
		}

		//Solve
		if(!unsat){
			vector<Literal> assumpts;
			Solution* sol = new Solution(true, false, modes.nbmodels, assumpts);
			unsat = !d->solve(sol);
			if (modes.verbosity >= 1) {
				reportf("===============================================================================\n");
			}
		}

		if(unsat){
			fprintf(getOutputFile(), "UNSAT\n");
			if(modes.verbosity >= 1){
				reportf("UNSATISFIABLE\n");
			}
		}

		if(modes.verbosity >= 1){
			d->printStatistics();
		}

		MinisatID::closeOutput();

		//#ifdef NDEBUG
		//		exit(unsat ? 20 : 10);     // (faster than "return", which will invoke the destructor for 'Solver')
		//#else
		returnvalue = unsat ? 20 : 10;
		//#endif

	} catch (idpexception& e) {
		reportf(e.what());
		reportf("Program will abort.\n");
		d->printStatistics();
	} catch (int) {
		reportf("Unexpected error caught, program will abort.\n");
		d->printStatistics();
	}

	return returnvalue;
}

///////
// PARSE CODE
///////

/**
 * Returns a data object representing the solver configuration from the input theory.
 * If the input theory was already found to be unsatisfiable, an empty shared pointer is returned.
 */
pData parse() {
	yyinit();

	try {
		/*ecnfparse();*/
		yyparse();
	} catch (idpexception& e) {
		if (unsatfound) {
			std::cerr << "Unsat detected during parsing.\n";
		} else {
			char s[300];
			sprintf(s, "Parse error: Line %d, column %d, on \"%s\": %s", lineNo, charPos, yytext, e.what());
			throw idpexception(s);
		}
	}

	pData d = getData();

	yydestroy();
	//There is still a memory leak of about 16 Kb in the flex scanner, which is inherent to the flex C scanner

	if (unsatfound) { //UNSAT so empty shared pointer
		return shared_ptr<WrappedLogicSolver> ();
	}

	return d;
}

///////
// Debugging - information printing
///////

static void SIGINT_handler(int signum) {
	//printStats(s);
	throw idpexception("*** INTERRUPTED ***\n");
}
