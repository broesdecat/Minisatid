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
#include <errno.h>
#include <iostream>
#include <fstream>
#include <signal.h>
#include <tr1/memory>
#include <argp.h>

#include "solvers/external/ExternalInterface.hpp"
#include "solvers/Unittests.hpp"
#include "solvers/parser/Lparseread.hpp"
#include "solvers/parser/PBread.hpp"

#if defined(__linux__)
#include <fpu_control.h>
#endif

using namespace std::tr1;
using namespace MinisatID;

ECNF_mode modes;

namespace MinisatID {
class SolverInterface;
typedef shared_ptr<SolverInterface> pData;
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

//Class to manage a read-only file
class FileR {
private:
	bool opened;
	FILE* file;

	FileR(const FileR &);
	FileR & operator=(const FileR &);

public:
	FileR(FILE* file) :
		opened(false), file(file) {
	}
	FileR(const char* name) :
		opened(false), file(fopen(name, "r")) {
		if (file == NULL) {
			char s[100];
			sprintf(s, "`%s' is not a valid filename or not readable.\n", name);
			throw idpexception(s);
		}
		opened = true;
	}

	~FileR() {
		if (opened) {
			fclose(file);
		}
	}

	void close() {
		if (opened) {
			opened = false;
			fclose(file);
		}
	}
	FILE* getFile() {
		return file;
	}
};

const char *argp_program_version = "minisatid 2.1.20";
const char *argp_program_bug_address = "<krr@cs.kuleuven.be>";

/* Program documentation. */
static char doc[] =
		"Courtesy of the KRR group at K.U. Leuven, Belgium, more info available on \"http://dtai.cs.kuleuven.be/krr\".\n"
			"MinisatID is a model expansion system for propositional logic extended with aggregates "
			"and inductive definitions. Also lparse and opb languages are supported.\n";

/* A description of the arguments we accept. */
static char args_doc[] = "ARG1 ARG2";

/* The options we understand. */
static struct argp_option options[] = {
		{"models"		, 'n', "INT", 0,	"The number of models INT to search for"},
		{"verbosity"	, 0, "VERB", 0,		"The level of output INT to generate"},
		{"rnd-freq"		, 0, "FREQ", 0,		"The frequency FREQ (in [0..1]) with which to make a random choice"},
		{"decay"		, 0, "DEC", 0,		"The amount of decay DEC (in [0..1]) used by the SAT-solver"},
		{"polarity-mode", 0, "POL", 0,		"POL={\"true\", \"false\", \"rnd\"}: sets the default polarity choice of variables"},
		{"lparse"		, 'l', 0,  0,		"Treat input as the LParse ASP ground format"},
		{"opb"			, 'p', 0, 0,		"Treat input as the opb (Pseudo-boolean) format"},
		{"idclausesaving", 0, "ID", 0,		"INT={0,1}: 0=add clause on propagation, 1=save clause on propagation"},
		{"aggclausesaving", 0, "INT", 0,	"INT={0,1,2}: 0=add clause on propagation, 1=save clause on propagation, 2=save minimal reason"},
		{"remap"		, 'r', "BOOL", 0,	"BOOL={\"yes\",\"no\"}: remap literals from the input structure to a gap-less internal format"},
		{"watchedaggr"	, 'w', "BOOL", 0,	"BOOL={\"yes\",\"no\"}: use watched-literal datastructures to handle aggregate propagation"},
		{"randomize"	, 0, "BOOL", 0,		"BOOL={\"yes\",\"no\"}: randomly generate the SAT-solver random seed"},
		{"disableheur"	, 0, "BOOL", 0,		"BOOL={\"yes\",\"no\"}: disable the SAT-solver's heuristic"},
		{"defstrat "	, 0, "STRAT", 0,	"STRAT={\"breadth_first\", \"depth_first\"}: sets the unfounded-set search-strategy"},
		{"defsearch"	, 0, "SEARCH", 0,	"SEARCH={\"always\", \"adaptive\", \"lazy\"}: sets the unfounded-set search-frequency"},
		{"defsem"		, 0, "SEM", 0,		"SEM={\"stable\", \"wellfounded\"}: uses the chosen semantics to handle inductive definitions"},
		{ 0 } }; //Required end tuple

/*
		{ "verbose", 'v', 0, 0, "Produce verbose output" },
		{ "quiet", 'q', 0, 0,"Don't produce any output" },
		{ "silent", 's', 0, OPTION_ALIAS },
		{ "output", 'o', "FILE", 0,	"Output to FILE instead of standard output" },
		{ 0 } };*/

/* Used by main to communicate with parse_opt. */
struct ECNF_mode2 {
	double random_var_freq, var_decay;
	POLARITY polarity_mode;
	int verbosity;

	//rest
	int nbmodels; //Try to find at most this number of models
	DEFSEM sem; //Definitional semantics to be used
	DEFFINDCS defn_strategy; // Controls which propagation strategy will be used for definitions.                         (default always)
	DEFMARKDEPTH defn_search; // Controls which search type will be used for definitions.                                  (default include_cs)
	DEFSEARCHSTRAT ufs_strategy; //Which algorithm to use to find unfounded sets

	bool lparse;
	bool pb;
	bool remap;  //Whether he should remap the atom values from the input to fill up gaps in the numbering
	bool pw;	//use partially watched agg structures or not.
	bool randomize; // use random seed initialization for the SAT-solver
	bool disableheur; // turn off the heuristic of the sat solver, allowing more predictable behavior
	int idclausesaving; //0 = on propagation add clause to store, 1 = on propagation, generate explanation and save it, 2 = on propagation, generate reason and save it
	int aggclausesaving; //0 = on propagation add clause to store, 1 = on propagation, generate explanation and save it, 2 = on propagation, generate reason and save it
	char* files[2];
};

/* Parse a single option. */
static error_t parse_opt(int key, char *arg, struct argp_state *state) {
	/* Get the input argument from argp_parse, which we know is a pointer to our arguments structure. */
	struct ECNF_mode2 *args = static_cast<ECNF_mode2*>(state->input);

	switch (key) {
		/*case 'q':
		case 's':
			args->silent = 1;
			break;
		case 'v':
			args->verbose = 1;
			break;
		case 'o':
			args->output_file = arg;
			break;
		case ARGP_KEY_ARG:
			if (state->arg_num >= 2)
				// Too many arguments.
				argp_usage(state);
			args->args[state->arg_num] = arg;
			break;
		case ARGP_KEY_END:
			if (state->arg_num < 2)
				// Not enough arguments.
				argp_usage(state);
			break;*/
		default:
			return ARGP_ERR_UNKNOWN;
	}
	return 0;
}

/* Our argp parser. */
static struct argp argp = { options, parse_opt, args_doc, doc };

int main(int argc, char** argv) {
	std::set_new_handler(noMoreMem);

#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw);
	newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
	_FPU_SETCW(newcw);
	if (modes.verbosity >= 1)
		reportf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif

	double cpu_time = cpuTime();

	signal(SIGINT, SIGINT_handler);
#if defined(__linux__)
	signal(SIGHUP, SIGINT_handler);
#endif

	FILE* res = NULL;
	pData d;
	try {
		struct ECNF_mode2 arguments;

		/* Default values. */
		arguments.random_var_freq = 0.02;
		arguments.var_decay = 1 / 0.95;
		arguments.polarity_mode = polarity_stored;
		arguments.verbosity = 0;
		arguments.sem = WELLF;
		arguments.nbmodels = 1;
		arguments.defn_strategy = always;
		arguments.defn_search = include_cs;
		arguments.ufs_strategy = breadth_first;
		arguments.lparse = false;
		arguments.pb = false;
		arguments.remap = false;
		arguments.pw = true;
		arguments.randomize = false;
		arguments.disableheur = false;
		arguments.idclausesaving = 0;
		arguments.aggclausesaving = 2;

		/* Parse our arguments; every option seen by parse_opt will
		 be reflected in arguments. */
		argp_parse(&argp, argc, argv, 0, 0, &arguments);

		/*printf("ARG1 = %s\nARG2 = %s\nOUTPUT_FILE = %s\n"
			"VERBOSE = %s\nSILENT = %s\n",
				arguments.args[0],
				arguments.args[1],
				arguments.output_file,
				arguments.verbose ? "yes" : "no",
				arguments.silent ? "yes" : "no");*/
		exit(0);
		//parseCommandline(argc, argv);

		/**
		 * First argument: executable
		 * Second argument if provided: input file.
		 * Third argument if provided: output file.
		 */

		//Unittest injection here: pData d = unittestx(modes);

		//An outputfile is not allowed when the inputfile is piped (//TODO should add a -o argument for this)
		res = stdout; //Default write to stdout

		if (modes.verbosity > 0) {
			reportf("============================[ Problem Statistics ]=============================\n");
			reportf("|                                                                             |\n");
		}

		if (modes.lparse) {
			modes.aggr = true;
			modes.def = true;
			PropositionalSolver* p = new PropositionalSolver(modes);
			d = shared_ptr<SolverInterface> (p);
			Read* r = new Read(p);

			if (argc == 1) {
				reportf("Reading from standard input... Use '-h' or '--help' for help.\n");
				r->read(std::cin);
			} else if (argc > 1) {
				std::filebuf fb;
				fb.open(argv[1], std::ios::in);
				std::istream x(&fb);
				r->read(x);
				fb.close();
				//TODO duplicate, buggy code with original (non lparse) parsing.
			}
		} else if (modes.pb) { //PB
			modes.aggr = true;
			modes.mnmz = true;
			PropositionalSolver* p = new PropositionalSolver(modes);
			d = shared_ptr<SolverInterface> (p);
			PBRead* parser = new PBRead(p, argv[1]);
			parser->autoLin();
			parser->parse();
			delete parser;
		} else {
			if (argc == 1) { //Read from stdin
				reportf("Reading from standard input... Use '-h' or '--help' for help.\n");
				/*ecnfin*/
				yyin = stdin;
				if (modes.verbosity > 0) {
					reportf("============================[ Problem Statistics ]=============================\n");
					reportf("|                                                                             |\n");
				}

				d = parse();
			} else {
				FileR filer(argv[1]);
				if (argc > 2) {
					res = fopen(argv[2], "wb"); //TODO include in FileR object
				}

				/*ecnfin*/
				yyin = filer.getFile();
				d = parse();
				filer.close();
			}
		}

		if (modes.verbosity > 1) {
			reportf("Plain parsing finished, starting datastructure initialization\n");
		}

		if (d.get() != NULL && !d->finishParsing()) {
			d = shared_ptr<SolverInterface> ();
		}

		if (modes.verbosity >= 1) {
			double parse_time = cpuTime() - cpu_time;
			reportf("| Parsing time              : %7.2f s                                       |\n", parse_time);
		}

		bool ret = true;
		if (d.get() == NULL) {
			ret = false;
			if (modes.verbosity > 0) {
				reportf("===============================================================================\n"
						"Unsatisfiable found by parsing\n");
			}
		}

		if (ret) {
			ret = d->simplify();
			if (!ret) {
				if (modes.verbosity > 0) {
					reportf("===============================================================================\n"
							"Unsatisfiable found by unit propagation\n");
				}
			}
		}

		if (ret) {
			d->setRes(res);
			//FIXME ret = d->solveprintModels(modes.nbmodels);
		} else {
			//If UNSAT was detected before solving, it has to be printed separately at the moment
			//TODO clean up code so the printing is handled cleaner.
			if (res != NULL) {
				fprintf(res, "UNSAT\n"), fclose(res);
			}
			printf("UNSATISFIABLE\n");
		}

		printStats();
		//#ifdef NDEBUG
		//		exit(ret ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
		//#else
		return ret ? 10 : 20;
		//#endif

	} catch (idpexception& e) {
		reportf(e.what());
		reportf("Program will abort.\n");
		if (d.get() != NULL) {
			d->printStatistics();
		}
		return 1;
	} catch (int) {
		if (d.get() != NULL) {
			d->printStatistics();
		}
		return 1;
	}
}

/****************
 * Parsing code *
 ****************/

const char* hasPrefix(const char* str, const char* prefix) {
	int len = strlen(prefix);
	if (strncmp(str, prefix, len) == 0)
		return str + len;
	else
		return NULL;
}

void parseCommandline(int& argc, char** argv) {
	int i, j;
	const char* value;
	for (i = j = 0; i < argc; i++) {
		if ((value = hasPrefix(argv[i], "--lparse="))) {
			if (strcmp(value, "yes") == 0) {
				modes.lparse = true;
			} else if (strcmp(value, "no") == 0) {
				modes.lparse = false;
			} else {
				char s[100];
				sprintf(s, "Unknown choice %s for lparse mode\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--pb="))) {
			if (strcmp(value, "yes") == 0) {
				modes.pb = true;
			} else if (strcmp(value, "no") == 0) {
				modes.pb = false;
			} else {
				char s[100];
				sprintf(s, "Unknown choice %s for pb mode\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--idclausesaving="))) {
			int cs = (int) strtol(value, NULL, 10);
			if (cs == 0 && errno == EINVAL) {
				char s[100];
				sprintf(s, "Illegal idclausesaving level %s\n", value);
				throw idpexception(s);
			}
			modes.idclausesaving = cs;
		} else if ((value = hasPrefix(argv[i], "--aggclausesaving="))) {
			int cs = (int) strtol(value, NULL, 10);
			if (cs == 0 && errno == EINVAL) {
				char s[100];
				sprintf(s, "Illegal aggclausesaving level %s\n", value);
				throw idpexception(s);
			}
			modes.aggclausesaving = cs;
		} else if ((value = hasPrefix(argv[i], "--polarity-mode="))) {
			if (strcmp(value, "true") == 0) {
				modes.polarity_mode = polarity_true;
			} else if (strcmp(value, "false") == 0) {
				modes.polarity_mode = polarity_false;
			} else if (strcmp(value, "rnd") == 0) {
				modes.polarity_mode = polarity_rnd;
			} else {
				char s[100];
				sprintf(s, "Unknown choice of polarity-mode %s\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--defn-strategy="))) {
			if (strcmp(value, "always") == 0) {
				modes.defn_strategy = always;
			} else if (strcmp(value, "adaptive") == 0) {
				modes.defn_strategy = adaptive;
			} else if (strcmp(value, "lazy") == 0) {
				modes.defn_strategy = lazy;
			} else {
				char s[100];
				sprintf(s, "Illegal definition strategy %s\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--rnd-freq="))) {
			double rnd;
			if (sscanf(value, "%lf", &rnd) <= 0 || rnd < 0 || rnd > 1) {
				char s[100];
				sprintf(s, "Illegal rnd-freq constant %s\n", value);
				throw idpexception(s);
			}
			modes.random_var_freq = rnd;
		} else if ((value = hasPrefix(argv[i], "--decay="))) {
			double decay;
			if (sscanf(value, "%lf", &decay) <= 0 || decay <= 0 || decay > 1) {
				char s[100];
				sprintf(s, "Illegal decay constant %s\n", value);
				throw idpexception(s);
			}
			modes.var_decay = 1 / decay;
		} else if ((value = hasPrefix(argv[i], "--ufsalgo="))) {
			if (strcmp(value, "depth") == 0) {
				modes.ufs_strategy = depth_first;
			} else if (strcmp(value, "breadth") == 0) {
				modes.ufs_strategy = breadth_first;
			} else {
				char s[100];
				sprintf(s, "Unknown choice of unfounded set algorithm: %s\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--idsem="))) {
			if (strcmp(value, "wellf") == 0) {
				modes.sem = WELLF;
			} else if (strcmp(value, "stable") == 0) {
				modes.sem = STABLE;
			} else {
				char s[100];
				sprintf(s, "Unknown choice of unfounded set algorithm: %s\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--verbosity="))) {
			int verb = (int) strtol(value, NULL, 10);
			if (verb == 0 && errno == EINVAL) {
				char s[100];
				sprintf(s, "Illegal verbosity level %s\n", value);
				throw idpexception(s);
			}
			modes.verbosity = verb;
		} else if ((value = hasPrefix(argv[i], "--remap="))) {
			if (strcmp(value, "yes") == 0) {
				modes.remap = true;
			} else if (strcmp(value, "no") == 0) {
				modes.remap = false;
			} else {
				char s[100];
				sprintf(s, "Unknown choice %s for remap mode\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--disableheur="))) {
			if (strcmp(value, "yes") == 0) {
				modes.disableheur = true;
			} else if (strcmp(value, "no") == 0) {
				modes.disableheur = false;
			} else {
				char s[100];
				sprintf(s, "Unknown choice %s for disableheur mode\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--random="))) {
			if (strcmp(value, "yes") == 0) {
				modes.randomize = true;
			} else if (strcmp(value, "no") == 0) {
				modes.randomize = false;
			} else {
				char s[100];
				sprintf(s, "Unknown choice %s for random mode\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--pw="))) {
			if (strcmp(value, "yes") == 0) {
				modes.pw = true;
			} else if (strcmp(value, "no") == 0) {
				modes.pw = false;
			} else {
				char s[100];
				sprintf(s, "Unknown choice %s for pw mode\n", value);
				throw idpexception(s);
			}
		} else if ((value = hasPrefix(argv[i], "--n"))) {
			char* endptr;
			modes.nbmodels = strtol(value, &endptr, 0);
			if (modes.nbmodels < 0 || *endptr != '\0') {
				throw idpexception("Option `-nN': N must be a positive integer, or 0 to get all models.");
			}
		}/*else if ((value = hasPrefix(argv[i], "-o=")) || (value = hasPrefix(argv[i], "--outputfile="))){
		 res = fopen(argv[2], "wb");
		 if(res==NULL){
		 throw idpexception("The provided outputfile \"%s\" could not be opened.\n", value);
		 }
		 }*/else if ((value = hasPrefix(argv[i], "-h")) || (value = hasPrefix(argv[i], "--help"))) {
			printUsage();
			exit(0);
		} else if ((value = hasPrefix(argv[i], "-v")) || (value = hasPrefix(argv[i], "--version"))) {
			printVersion();
			exit(0);
		} else if (strncmp(argv[i], "-", 1) == 0) {
			char s[100];
			sprintf(s, "Unknown flag %s\n", argv[i]);
			throw idpexception(s);
		} else {
			argv[j++] = argv[i];
		}
	}
	argc = j;
}

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
		return shared_ptr<SolverInterface> ();
	}

	return d;
}

/**************************************
 * Debugging and information printing *
 **************************************/

static void SIGINT_handler(int signum) {
	//printStats(s);
	throw idpexception("*** INTERRUPTED ***\n");
}

void printStats() {
	//repair later + add extra stats
}
