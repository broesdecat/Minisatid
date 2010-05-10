#include <ctime>
#include <cstring>
#include <stdint.h>
#include <errno.h>

#include <signal.h>
#include <zlib.h>

#if defined(__linux__)
#include <fpu_control.h>
#endif

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

#include "solverfwd.h"
#include "SolverI.h"

#include "debug.h"

//TODO handle exit(x) with exception throwing instead, giving much cleaner code!!!

ECNF_mode modes;

class Data;
typedef shared_ptr<Data> pData;

extern pData getData		();

extern FILE* yyin;
extern int 	yyparse			();
extern void yydestroy		();
extern void yyinit			(/*pSolver s, pIDSolver ids, pAggSolver aggs*/);
extern bool unsatfound;
bool parseError = false;

//void 		initSolvers		(const pSolver& S, const pIDSolver& TS, const pAggSolver& AggS);

const char* hasPrefix		(const char* str, const char* prefix);
void 		parseCommandline(/*const pSolver&, const pIDSolver&, const pAggSolver&,*/ int& argc, char** argv);
pData 		parse			(/*const pSolver&, const pIDSolver&, const pAggSolver&,*/ const char* file);

void 		printStats		(/*pSolver solver*/);
static void SIGINT_handler	(int signum);
void 		printUsage		(char** argv);


//FIXME: adapt for modal solver
//wpSolver wps;
void		noMoreMem(){
	//Tries to reduce the memory of the solver by reducing the number of learned clauses
	//This keeps being called until enough memory is free or no more learned clauses can be/are deleted (causing abort).
//	TODO TODO FIXME
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
//		exit(3);
//	}
}

int main(int argc, char** argv) {
	reportf("This is MiniSAT-SMT 1.0\n");

	std::set_new_handler(noMoreMem);

/*	pSolver		S(new Solver());
	wps = wpSolver(S);
	pIDSolver	TS(new IDSolver());
	pAggSolver	AggS(new AggSolver());
    initSolvers(S, TS, AggS);*/

    parseCommandline(/*S, TS, AggS,*/ argc, argv);

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
	signal(SIGHUP, SIGINT_handler);

	if (argc == 1)
		reportf("Reading from standard input... Use '-h' or '--help' for help.\n");

	if(modes.verbosity>0){
		reportf("============================[ Problem Statistics ]=============================\n");
		reportf("|                                                                             |\n");
	}

    bool ret = false;
    FILE* res = NULL;
	try {
		res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

		pData d = parse(/*S, TS, AggS,*/ argv[1]);

		if(modes.verbosity>0){
			reportf("| Parsing time              : %7.2f s                                    |\n", cpuTime()-cpu_time);
		}

		if (modes.verbosity >= 1) {
			double parse_time = cpuTime() - cpu_time;
			reportf("| Parsing time              : %7.2f s                                       |\n", parse_time);
		}

		if(d.get()==NULL){
			ret = false;
			if(modes.verbosity>0){
				reportf("===============================================================================\n"
						"Unsatisfiable found by parsing\n");
			}
		}else{
			if (!d->simplify()) {
				if(modes.verbosity>0){
					reportf("===============================================================================\n"
							"Solved by unit propagation\n");
				}
				ret = false;
			}else{
				d->setNbModels(modes.nbmodels);
				d->setRes(res);

				ret = d->solve();
			}
		}

		//TODO printStats(S);
	}catch(bad_alloc e){ //FIXME: handle all these elegantly
		reportf("Memory overflow, cannot continue solving.\n"); exit(3);
	}catch(int ex){
		reportf("Unexpected exception thrown as int with code %d\n", ex);
		exit(3);
	}

	if(!ret){
		if (res != NULL){
			fprintf(res, "UNSAT\n"), fclose(res);
		}
		printf("UNSATISFIABLE\n");
	}

#ifdef NDEBUG
    exit(ret ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
    return ret?10:20;
#endif
}

/*void initSolvers(const pSolver& S, const pIDSolver& TS, const pAggSolver& AggS){
	S->setIDSolver(TS);
	S->setAggSolver(AggS);
	TS->setSolver(S);
	TS->setAggSolver(AggS);
	AggS->setSolver(S);
	AggS->setIDSolver(TS);
}*/

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

void parseCommandline(/*const pSolver& S, const pIDSolver& TS, const pAggSolver& AggS,*/ int& argc, char** argv){
    int         i, j;
    const char* value;
    for (i = j = 0; i < argc; i++){
        if ((value = hasPrefix(argv[i], "-polarity-mode="))){
            if (strcmp(value, "true") == 0){
               modes.polarity_mode = polarity_true;
            }else if (strcmp(value, "false") == 0){
            	modes.polarity_mode = polarity_false;
            }else if (strcmp(value, "rnd") == 0){
            	modes.polarity_mode = polarity_rnd;
            }else{
                reportf("ERROR! unknown polarity-mode %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-defn_strategy="))){
            if (strcmp(value, "always") == 0){
            	modes.defn_strategy = always;
            }else if (strcmp(value, "adaptive") == 0){
            	modes.defn_strategy = adaptive;
			}else if (strcmp(value, "lazy") == 0){
				modes.defn_strategy = lazy;
			}else{
                reportf("ERROR! illegal definition strategy %s\n", value);
                exit(0);
			}
        }else if ((value = hasPrefix(argv[i], "-defn_search="))){
            if (strcmp(value, "include_cs") == 0)
            	modes.defn_search = include_cs;
            else if (strcmp(value, "stop_at_cs") == 0)
            	modes.defn_search = stop_at_cs;
            else{
                reportf("ERROR! illegal definition ssearch type %s\n", value);
                exit(0);
            }
        }else if ((value = hasPrefix(argv[i], "-rnd-freq="))){
            double rnd;
            if (sscanf(value, "%lf", &rnd) <= 0 || rnd < 0 || rnd > 1){
                reportf("ERROR! illegal rnd-freq constant %s\n", value);
                exit(0); }
            modes.random_var_freq = rnd;
        }else if ((value = hasPrefix(argv[i], "-decay="))){
            double decay;
            if (sscanf(value, "%lf", &decay) <= 0 || decay <= 0 || decay > 1){
                reportf("ERROR! illegal decay constant %s\n", value);
                exit(0); }
            modes.var_decay = 1 / decay;
        }else if ((value = hasPrefix(argv[i], "-ufsalgo="))){
			if (strcmp(value, "depth") == 0){
				modes.ufs_strategy = depth_first;
			}else if(strcmp(value, "breadth") == 0){
				modes.ufs_strategy = breadth_first;
			}else{
				reportf("ERROR! unknown choice of unfounded set algorithm: %s\n", value);
				exit(0);
			}
        }else if ((value = hasPrefix(argv[i], "-idsem="))){
			if (strcmp(value, "wellf") == 0){
				modes.sem = WELLF;
			}else if(strcmp(value, "stable") == 0){
				modes.sem = STABLE;
			}else{
				reportf("ERROR! unknown choice of unfounded set algorithm: %s\n", value);
				exit(0);
			}
        }else if ((value = hasPrefix(argv[i], "-verbosity="))){
            int verb = (int)strtol(value, NULL, 10);
            if (verb == 0 && errno == EINVAL){
                reportf("ERROR! illegal verbosity level %s\n", value);
                exit(0); }
           	modes.verbosity=verb;
        }else if (strncmp(&argv[i][0], "-n",2) == 0){
            char* endptr;
            modes.nbmodels = strtol(&argv[i][2], &endptr, 0);
            if (modes.nbmodels < 0 || *endptr != '\0') {
               reportf("ERROR! option `-nN': N must be a positive integer, or 0 to get all models.");
               exit(0);
            }
        }else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "-help") == 0 || strcmp(argv[i], "--help") == 0){
            printUsage(argv);
            exit(0);
        }else if (strncmp(argv[i], "-", 1) == 0){
            reportf("ERROR! unknown flag %s\n", argv[i]);
            exit(0);
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
pData parse(/*const pSolver& S, const pIDSolver& TS, const pAggSolver& AggS,*/ const char* file){
   	yyinit(/*S, TS, AggS*/);
	yyin = fopen(file,"r");
	if(!yyin) {
		reportf("`%s' is not a valid filename or not readable.\n", file);
		exit(1);
	}
	yyparse();

	if(unsatfound){
		return shared_ptr<Data>();
	}

	pData d = getData();

	yydestroy();
	fclose(yyin);
	if(parseError){
		reportf("At least one parsing error, program will ex;it.\n");
		exit(3);
	}

	d->finishParsing();

	return d;
}

/**************************************
 * Debugging and information printing *
 **************************************/

static void SIGINT_handler(int signum) {
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    //printStats(s);
    //reportf("\n"); reportf("*** INTERRUPTED ***\n");
    exit(1);
}

void printUsage(char** argv) {
	reportf("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n\n", argv[0]);
	reportf("OPTIONS:\n\n");
	reportf("  -n<num>        = find <num> models (0=all; default 1)\n");
	reportf("  -polarity-mode = {true,false,rnd}\n");
	reportf("  -decay         = <num> [ 0 - 1 ]\n");
	reportf("  -rnd-freq      = <num> [ 0 - 1 ]\n");
	reportf("  -verbosity     = {0,1,2}\n");
	reportf("  -defn_strategy = {always,adaptive,lazy}\n");
	reportf("  -defn_search   = {include_cs,stop_at_cs}\n");
	reportf("  -maxruntime    = <num> (in seconds)\n");
	reportf("\n");
}

void printStats(/*pSolver solver*/){
	//TODO repair later + add extra stats
}
