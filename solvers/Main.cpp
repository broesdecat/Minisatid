/************************************************************************************
Copyright (c) 2006-2009, Maarten Mariën
Copyright (c) 2009-2010, Broes De Cat

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

#if defined(__linux__)
#include <fpu_control.h>
#endif

#if defined(__linux__)
#ifdef _MSC_VER
#include <ctime>

static inline double cpuTime(void) {
    return (double)clock() / CLOCKS_PER_SEC;
}

#else
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}
#endif
#else
static inline double cpuTime(void) { return 0; }
#endif

#include "solvers/external/ExternalInterface.hpp"

#include "solvers/Unittests.hpp"
#include "solvers/parser/Lparseread.hpp"

ECNF_mode modes;

#include <tr1/memory>

using namespace std::tr1;

class SolverInterface;
typedef shared_ptr<SolverInterface> pData;

extern char * 	yytext;
extern int 		lineNo;
extern int 		charPos;
extern pData 	getData		();

//extern FILE*	ecnfin;
//extern int	ecnfparse	();
extern FILE* yyin;
extern int 	yyparse			();
extern void yydestroy		();
extern void yyinit			();
extern bool unsatfound;

const char* hasPrefix		(const char* str, const char* prefix);
void 		parseCommandline(int& argc, char** argv);
pData 		parse			();

void 		printStats		();
static void SIGINT_handler	(int signum);
void 		printUsage		(char** argv);

void		noMoreMem(){
	//Tries to reduce the memory of the solver by reducing the number of learned clauses
	//This keeps being called until enough memory is free or no more learned clauses can be/are deleted (causing abort).
	throw idpexception("The solver ran out of memory.\n");
//	bool reducedmem = false;
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
//	if(!reducedmem){
//		reportf("There is no more memory to allocate, program aborting.\n");
//		throw new idpexception();
//	}
}

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
	try{
		parseCommandline(argc, argv);

		/**
		 * First argument: executable
		 * Second argument if provided: input file.
		 * Third argument if provided: output file.
		 */

		//pData d = unittest(modes);
		//pData d = unittest2(modes);
		//pData d = unittest3(modes);

		//An outputfile is not allowed when the inputfile is piped (//TODO should add a -o argument for this)
		/*ecnfin*/yyin = stdin; //Default read from stdin
		res = stdout; 	//Default write to stdout

		pData d;
		if(modes.lparse){
			PropositionalSolver* p = new PropositionalSolver(modes);
			d = shared_ptr<SolverInterface>(p);
			Read* r = new Read(p);

			if(argc==1){
				reportf("Reading from standard input... Use '-h' or '--help' for help.\n");
				r->read(cin);
			}else if(argc>1){
				filebuf fb;
				fb.open(argv[1],ios::in);
				istream x(&fb);
				r->read(x);
				//TODO duplicate, buggy code with original (non lparse) parsing.
			}

			if(modes.verbosity>0){
				reportf("============================[ Problem Statistics ]=============================\n");
				reportf("|                                                                             |\n");
			}


		}else{
			if(argc==1){
				reportf("Reading from standard input... Use '-h' or '--help' for help.\n");
			}else if(argc>1){
				/*ecnfin*/yyin = fopen(argv[1], "r");
				if(!/*ecnfin*/yyin) {
					char s[100]; sprintf(s, "`%s' is not a valid filename or not readable.\n", argv[1]);
					throw idpexception(s);
				}
				if(argc>2){
					res = fopen(argv[2], "wb");
				}
			}

			if(modes.verbosity>0){
				reportf("============================[ Problem Statistics ]=============================\n");
				reportf("|                                                                             |\n");
			}

			d = parse();
		}

		if(/*ecnfin*/yyin != stdin){
			fclose(/*ecnfin*/yyin);
		}

		if(modes.verbosity>0){
			reportf("| Parsing time              : %7.2f s                                    |\n", cpuTime()-cpu_time);
		}

		if (modes.verbosity >= 1) {
			double parse_time = cpuTime() - cpu_time;
			reportf("| Parsing time              : %7.2f s                                       |\n", parse_time);
		}

		bool ret = true;
		if(d.get()==NULL){
			ret = false;
			if(modes.verbosity>0){
				reportf("===============================================================================\n"
						"Unsatisfiable found by parsing\n");
			}
		}

		if(ret){
			ret = d->simplify();
			if (!ret) {
				if(modes.verbosity>0){
					reportf("===============================================================================\n"
							"Unsatisfiable found by unit propagation\n");
				}
			}
		}

		if(ret){
			d->setNbModels(modes.nbmodels);
			d->setRes(res);
			ret = d->solve();
		}else{
			//If UNSAT was detected before solving, it has to be printed separately at the moment
			//TODO clean up code so the printing is handled cleaner.
			if (res != NULL){
				fprintf(res, "UNSAT\n"), fclose(res);
			}
			printf("UNSATISFIABLE\n");
		}

		printStats();
#ifdef NDEBUG
		exit(ret ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
		return ret?10:20;
#endif

	}catch(idpexception& e){
		reportf(e.what());
		reportf("Program will abort.\n");
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

void parseCommandline(int& argc, char** argv){
    int         i, j;
    const char* value;
    for (i = j = 0; i < argc; i++){
    	if ((value = hasPrefix(argv[i], "-lparse"))){
			modes.lparse = true;
			modes.aggr = true;
			modes.def = true;
    	}else if ((value = hasPrefix(argv[i], "-polarity-mode="))){
            if (strcmp(value, "true") == 0){
               modes.polarity_mode = polarity_true;
            }else if (strcmp(value, "false") == 0){
            	modes.polarity_mode = polarity_false;
            }else if (strcmp(value, "rnd") == 0){
            	modes.polarity_mode = polarity_rnd;
            }else{
				char s[100]; sprintf(s, "Unknown choice of polarity-mode %s\n", value);
				throw idpexception(s);
            }
        }else if ((value = hasPrefix(argv[i], "-defn-strategy="))){
            if (strcmp(value, "always") == 0){
            	modes.defn_strategy = always;
            }else if (strcmp(value, "adaptive") == 0){
            	modes.defn_strategy = adaptive;
			}else if (strcmp(value, "lazy") == 0){
				modes.defn_strategy = lazy;
			}else{
				char s[100]; sprintf(s, "Illegal definition strategy %s\n", value);
				throw idpexception(s);
			}
        }else if ((value = hasPrefix(argv[i], "-defn-search="))){
            if (strcmp(value, "include_cs") == 0)
            	modes.defn_search = include_cs;
            else if (strcmp(value, "stop_at_cs") == 0)
            	modes.defn_search = stop_at_cs;
            else{
				char s[100]; sprintf(s, "Illegal definition search type %s\n", value);
				throw idpexception(s);
            }
        }else if ((value = hasPrefix(argv[i], "-rnd-freq="))){
            double rnd;
            if (sscanf(value, "%lf", &rnd) <= 0 || rnd < 0 || rnd > 1){
				char s[100]; sprintf(s, "Illegal rnd-freq constant %s\n", value);
				throw idpexception(s);
            }
            modes.random_var_freq = rnd;
        }else if ((value = hasPrefix(argv[i], "-decay="))){
            double decay;
            if (sscanf(value, "%lf", &decay) <= 0 || decay <= 0 || decay > 1){
				char s[100]; sprintf(s, "Illegal decay constant %s\n", value);
				throw idpexception(s);
            }
            modes.var_decay = 1 / decay;
        }else if ((value = hasPrefix(argv[i], "-ufsalgo="))){
			if (strcmp(value, "depth") == 0){
				modes.ufs_strategy = depth_first;
			}else if(strcmp(value, "breadth") == 0){
				modes.ufs_strategy = breadth_first;
			}else{
				char s[100]; sprintf(s, "Unknown choice of unfounded set algorithm: %s\n", value);
				throw idpexception(s);
			}
        }else if ((value = hasPrefix(argv[i], "-idsem="))){
			if (strcmp(value, "wellf") == 0){
				modes.sem = WELLF;
			}else if(strcmp(value, "stable") == 0){
				modes.sem = STABLE;
			}else{
				char s[100]; sprintf(s, "Unknown choice of unfounded set algorithm: %s\n", value);
				throw idpexception(s);
			}
        }else if ((value = hasPrefix(argv[i], "-verbosity="))){
            int verb = (int)strtol(value, NULL, 10);
            if (verb == 0 && errno == EINVAL){
				char s[100]; sprintf(s, "Illegal verbosity level %s\n", value);
				throw idpexception(s);
            }
           	modes.verbosity=verb;
        }else if (strncmp(&argv[i][0], "-n",2) == 0){
            char* endptr;
            modes.nbmodels = strtol(&argv[i][2], &endptr, 0);
            if (modes.nbmodels < 0 || *endptr != '\0') {
				throw idpexception("Option `-nN': N must be a positive integer, or 0 to get all models.");
            }
        }else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "-help") == 0 || strcmp(argv[i], "--help") == 0){
            printUsage(argv);
            exit(0);
        }else if (strncmp(argv[i], "-", 1) == 0){
			char s[100]; sprintf(s, "Unknown flag %s\n", argv[i]);
			throw idpexception(s);
        }else{
            argv[j++] = argv[i];
        }
    }
    argc = j;
}

/**
 * Returns a data object representing the solver configuration from the input theory.
 * If the input theory was already found to be unsatisfiable, an empty shared pointer is returned.
 */
pData parse(){
	yyinit();

	try{
		/*ecnfparse();*/
		yyparse();
	}catch(idpexception& e){
		if(unsatfound){
			cerr << "Unsat detected during parsing.\n";
		}else{
			char s[300];
			sprintf(s, "Parse error: Line %d, column %d, on \"%s\": %s", lineNo, charPos, yytext, e.what());
			throw idpexception(s);
		}
	}

	pData d = getData();

	yydestroy();
    //There is still a memory leak of about 16 Kb in the flex scanner, which is inherent to the flex C scanner

	if(unsatfound || !d->finishParsing()){ //UNSAT so empty shared pointer
		return shared_ptr<SolverInterface>();
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

void printUsage(char** argv) {
	reportf("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n\n", argv[0]);
	reportf("OPTIONS:\n\n");
	reportf("  -n<num>        = find <num> models (0=all; default 1)\n");
	reportf("  -polarity-mode = {true,false,rnd}\n");
	reportf("  -decay         = <num> [ 0 - 1 ]\n");
	reportf("  -rnd-freq      = <num> [ 0 - 1 ]\n");
	reportf("  -verbosity     = {0,1,2}\n");
	reportf("  -defn-strategy = {always,adaptive,lazy}\n");
	reportf("  -defn-search   = {include_cs,stop_at_cs}\n");
	reportf("  -maxruntime    = <num> (in seconds)\n");
	reportf("\n");
}

void printStats(){
	//repair later + add extra stats
}
