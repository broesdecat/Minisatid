#include <ctime>
#include <cstring>
#include <stdint.h>
#include <errno.h>

#include <cmath> // for "pow"

#include <signal.h>
#include <zlib.h>

#include "MODSolver.h"
#include "SolverTypes.h"

extern int verbosity;
extern Parameters params;

#if defined(__linux__)
#include <fpu_control.h>
#endif

//=================================================================================================
// DIMACS Parser:

#define CHUNK_LIMIT 1048576

class StreamBuffer {
    gzFile  in;
    char    buf[CHUNK_LIMIT];
    int     pos;
    int     size;

    void assureLookahead() {
        if (pos >= size) {
            pos  = 0;
            size = gzread(in, buf, sizeof(buf)); } }

public:
    StreamBuffer(gzFile i) : in(i), pos(0), size(0) {
        assureLookahead(); }

    int  operator *  () { return (pos >= size) ? EOF : buf[pos]; }
    void operator ++ () { pos++; assureLookahead(); }
};

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

template<class B>
static void skipWhitespace(B& in) {
    while ((*in >= 9 && *in <= 13) || *in == 32)
        ++in; }

template<class B>
static void skipLine(B& in) {
    for (;;){
        if (*in == EOF || *in == '\0') return;
        if (*in == '\n') { ++in; return; }
        ++in; } }

template<class B>
static int parseInt(B& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') reportf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }

template<class B>
static void readClause(B& in, MODSolver* S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        lits.push( (parsed_lit > 0) ? Lit(var) : ~Lit(var) );
    }
}

template<class B>
static bool match(B& in, const char* str) {
    for (; *str != 0; ++str, ++in)
        if (*str != *in)
            return false;
    return true;
}

#define ParseError(format, args...) ( fflush(stdout), fprintf(stderr, "PARSE ERROR! "), fprintf(stderr, format, ## args), fflush(stderr), exit(3) )


////////START OF EXTENSIONS
/*
 * AGGREGATE GROUND FORMAT:
 *
 * aggL HEAD SET BOUND 0
 * aggG HEAD SET BOUND 0
 *
 * where agg one from {Max, Min, Prod, Sum, Card}
 *
 * semantics:
 * aggL then HEAD <=> aggvalue =< BOUND
 * aggG then HEAD <=> BOUND >= aggvalue
 */

template<class B>
static void parse_Aggr(B& in, MODSolver* S, AggrType type) {
	char boundtype, deftype;
	if(*in==' '){
		 ParseError("No bound comparison operator for the aggregate (L or G) was given.\n");
	}
	if(*in==' '){
		ParseError("No aggregate semantics (D or C) were given.\n");
	}
	deftype = *in; ++in;
	bool defined, lower;
	if(deftype=='D'){
		defined = true;
	}else if(deftype=='C'){
		defined = false;
	}else{
		ParseError("Only completion (C) or definitional (D) semantics are possible for aggregates.\n");
	}
	boundtype = *in; ++in;
	if(boundtype=='L'){
		lower = true;
	}else if(boundtype=='G'){
		lower = false;
	}else{
		ParseError("Only LEQ (L) or GEQ (G) bound semantics are possible for aggregates.\n");
	}

	++in;

    int defn = parseInt(in);
    if (defn<=0)
        ParseError("Defining literal of aggregate expression has to be an atom (found %d).\n",defn);
    else defn--;
    int set_id = parseInt(in);
    int bound = parseInt(in);
    int zero = parseInt(in);
    if (zero != 0)
        ParseError("Aggregate expression has to be closed with '0' (found %d).\n",zero);
    S->addAggrExpr(false, defn,set_id,bound,lower,type, defined);
}
/////////END OF EXTENSIONS


template<class B>
static void parse_ECNF_main(B& in, MODSolver* S) { // NOTE: this parser does not read translation information.
    vec<Lit> lits;
    for (;;){
        skipWhitespace(in);
        char c=*in;
        if (c==EOF)
            break;
        else if (c == 'p' || c == 'c')
            skipLine(in);
        else {
            switch (c) {
				case 'C':
                    if (match(in,"Card")){
                    	parse_Aggr(in, S, SUM);
                    }else { // conjunctive rule.
                        ++in;
                        readClause(in, S, lits);
                        S->addRule(false, true, lits);
                    }
                    break;
                case 'D': // disjunctive rule.
                    ++in;
                    readClause(in, S, lits);
                    S->addRule(false, false, lits);
                    break;
                case 'M':
                    ++in;
                    if (*in == 'i' && match(in,"in"))
                        parse_Aggr(in, S, MIN);
                    else if (*in == 'a' && match(in,"ax"))
                        parse_Aggr(in, S, MAX);
                    else if (*in == 'n' && match(in,"nmz")) {
                        readClause(in, S, lits);
                        S->subsetMinimize(lits);
                    }else
                        ParseError("Unexpected char '%c' after 'M' (expecting \"Min\", \"Max\" or \"Mnmz\").\n",*in);
                    break;
                case 'P':
                    if (match(in,"Prod"))
                        parse_Aggr(in, S, PROD);
                    else
                        ParseError("Unexpected char '%c' after 'P' (expecting \"Prod\").\n",*in);
                    break;
                case 'S':
                    ++in;
                    if (*in == 'e' && match(in,"et")) {
                        int set_id = parseInt(in); // Note that set_id 0 cannot exist.
                        readClause(in, S, lits);
                        vec<int> w(lits.size(),1); // Treat CARD as SUM with all weights =1.
                        S->addSet(false, set_id,lits,w);
                    } else if (*in == 'u' && match(in,"um"))
                        parse_Aggr(in, S, SUM);
                    else
                        ParseError("Unexpected char '%c' after 'S' (expecting \"Set\" or \"Sum\").\n",*in);
                    break;
                case 'W':
                    if (match(in,"WSet")) {
                        int set_id = parseInt(in); // Note that set_id 0 cannot exist.

                        int     parsed_lit, var;
                        lits.clear();
                        vec<int> weights;
                        for (;;){
                            parsed_lit = parseInt(in);
                            if (parsed_lit == 0) break;
                            var = abs(parsed_lit)-1;
                            lits.push( (parsed_lit > 0) ? Lit(var) : ~Lit(var) );
                            if (*in != '=')
                                ParseError("Encountered weightless literal in \"WSet\" declaration.\n");
                            ++in;
                            parsed_lit = parseInt(in);
                            weights.push(parsed_lit);
                        }
                        S->addSet(false, set_id,lits,weights);
                    } else
                        ParseError("Unexpected char '%c' after 'W' (expecting \"WSet\").\n",*in);
                    break;
                default:
                    readClause(in, S, lits);
                    S->addClause(false, lits);
                    break;
            }
        }
    }

    S->finishDatastructures();
}

template<class B>
static void parse_main(B& in, MODSolver* S) {
    bool ecnf = false;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF)
            break;
        else if (*in == 'p'){
            ++in; ++in;
            if (match(in, "cnf")){
                int vars    = parseInt(in);
                int clauses = parseInt(in);
                if (verbosity>=1) {
                    reportf("|  Number of variables:  %-12d                                         |\n", vars);
                    reportf("|  Number of clauses:    %-12d                                         |\n", clauses);
                }
                ecnf=true;
                break;
            }else if (match(in,"ecnf")) {
                ecnf=true;
                if (verbosity>=1)
                    reportf("| Reading ECNF file.                                                          |\n");
                for (;*in!='\n';) {
                    while (*in == 9 || *in == 11 || *in == 12 || *in == 13 || *in == 32) ++in;
                    if (*in==EOF || *in=='\0' || *in=='\n') break;
                    if (*in=='d' && match(in,"def")) {
                        if (verbosity>=1)
                            reportf("|    May contain inductive definitions.                                       |\n");
                        params.def = true;
                    } else if (*in=='e' && match(in,"eu")) {
                        if (verbosity>=1)
                            reportf("|    May contain exists unique statements (registered as at-most-one).        |\n");
                    } else if (*in=='a') {
                        ++in;
                        if (*in=='m' && match(in,"mo")) {
                            if (verbosity>=1)
                                reportf("|    May contain at most one statements                                  |\n");
                        } else if (*in=='g' && match(in,"ggr")) {
                            if (verbosity>=1)
                                reportf("|    May contain aggregate expressions.                                       |\n");
                            params.aggr = true;
                        } else
                            ParseError("Unexpected ECNF extension type (known: \"def\", \"eu\", \"amn\", \"aggr\"); stuck on '%c'.\n",*in);
                    } else if (*in=='m' && match(in,"mnmz")) {
                        if (verbosity>=1)
                            reportf("|    May contain an optimize statement.                                       |\n");
                        params.mnmz = true;
                    } else
                        ParseError("Unexpected ECNF extension type (known: \"def\", \"eu\", \"amn\", \"aggr\"); stuck on '%c'.\n",*in);
                }
                ++in;
                break;
            }else
                ParseError("Unexpected char: %c\n", *in);
        } else if (*in == 'c' || *in == 'p') {
            if (match(in, "c grounder error"))
                reportf("There was a grounding error; MiniSat can't continue solving.\n"), exit(20);
            else
                skipLine(in);
        } else
            ParseError("Unexpected char: %c\n", *in);
    }
    if (ecnf){
    	parse_ECNF_main(in, S);
    }else{
    	reportf("Format no longer supported.\n"), exit(1);
    }
}

// Inserts problem into solver.
//
static void parse(gzFile input_stream, MODSolver* S) {
    StreamBuffer in(input_stream);
    parse_main(in, S); }

//=================================================================================================

static void SIGINT_handler(int signum) {
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    //printStats(solver);
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    exit(1);
}


//=================================================================================================
// Main:

static void printUsage(char** argv)
{
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


static const char* hasPrefix(const char* str, const char* prefix)
{
    int len = strlen(prefix);
    if (strncmp(str, prefix, len) == 0)
        return str + len;
    else
        return NULL;
}


int main2(int argc, char** argv)
{
    MODSolver* S = new MODSolver();

    int         i, j;
    int         N = 1;
    const char* value;
    for (i = j = 0; i < argc; i++){
        if ((value = hasPrefix(argv[i], "-polarity-mode="))){
            if (strcmp(value, "true") == 0)
            	params.polarity_mode = polarity_true;
            else if (strcmp(value, "false") == 0)
            	params.polarity_mode = polarity_false;
            else if (strcmp(value, "rnd") == 0)
            	params.polarity_mode = polarity_rnd;
            else{
                reportf("ERROR! unknown polarity-mode %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-defn_strategy="))){
            if (strcmp(value, "always") == 0)
            	params.defn_strategy = always;
            else if (strcmp(value, "adaptive") == 0)
            	params.defn_strategy = adaptive;
            else if (strcmp(value, "lazy") == 0)
            	params.defn_strategy = lazy;
            else{
                reportf("ERROR! illegal definition strategy %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-defn_search="))){
            if (strcmp(value, "include_cs") == 0)
            	params.defn_search = include_cs;
            else if (strcmp(value, "stop_at_cs") == 0)
            	params.defn_search = stop_at_cs;
            else{
                reportf("ERROR! illegal definition ssearch type %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-rnd-freq="))){
            double rnd;
            if (sscanf(value, "%lf", &rnd) <= 0 || rnd < 0 || rnd > 1){
                reportf("ERROR! illegal rnd-freq constant %s\n", value);
                exit(0); }
            params.random_var_freq = rnd;

        }else if ((value = hasPrefix(argv[i], "-decay="))){
            double decay;
            if (sscanf(value, "%lf", &decay) <= 0 || decay <= 0 || decay > 1){
                reportf("ERROR! illegal decay constant %s\n", value);
                exit(0); }
           params.var_decay = 1 / decay;

        }else if ((value = hasPrefix(argv[i], "-ufsalgo="))){
			if (strcmp(value, "depth") == 0){
				params.ufs_strategy = depth_first;
			}else if(strcmp(value, "breadth") == 0){
				params.ufs_strategy = breadth_first;
			}else{
				reportf("ERROR! unknown choice of unfounded set algorithm: %s\n", value);
				exit(0);
			}

        }else if ((value = hasPrefix(argv[i], "-verbosity="))){
            int verb = (int)strtol(value, NULL, 10);
            if (verb == 0 && errno == EINVAL){
                reportf("ERROR! illegal verbosity level %s\n", value);
                exit(0); }
            verbosity = verb;

        }else if ((value = hasPrefix(argv[i], "-maxruntime="))){
        	params.maxruntime = (double)strtol(value, NULL, 10);
            if (params.maxruntime <= 0.0) {
                reportf("ERROR! maxruntime should be bigger then zero.\n");
                exit(0); }

        }else if (strncmp(&argv[i][0], "-n",2) == 0){
            char* endptr;
            N = strtol(&argv[i][2], &endptr, 0);
            if (N < 0 || *endptr != '\0') {
               reportf("ERROR! option `-nN': N must be a positive integer, or 0 for all models.");
               exit(0);
            }
        }else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "-help") == 0 || strcmp(argv[i], "--help") == 0){
            printUsage(argv);
            exit(0);

        }else if (strncmp(argv[i], "-", 1) == 0){
            reportf("ERROR! unknown flag %s\n", argv[i]);
            exit(0);

        }else
            argv[j++] = argv[i];
    }
    argc = j;


    if (verbosity>=1)
        reportf("This is MiniSat 2.0 beta\n");
#if defined(__linux__)
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
    if (verbosity>=1)
        reportf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
    double cpu_time = cpuTime();

    signal(SIGINT,SIGINT_handler);
    signal(SIGHUP,SIGINT_handler);

    if (argc == 1)
        reportf("Reading from standard input... Use '-h' or '--help' for help.\n");

    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        reportf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

    if (verbosity>=1) {
        reportf("============================[ Problem Statistics ]=============================\n");
        reportf("|                                                                             |\n");
    }

    bool ret = false;

    try{
		parse(in, S);

		gzclose(in);
		FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

		if (verbosity>=1) {
			double parse_time = cpuTime() - cpu_time;
			reportf("| Parsing time              : %7.2f s                                       |\n", parse_time);
		}

		S->solve();
	}catch(int e){
		if(e==memOVERFLOW){
			reportf("Memory overflow");
			exit(33);
		}else if(e==theoryUNSAT){
			reportf("Theory UNSAT");
			ret=false;
		}
	}

#ifdef NDEBUG
    exit(ret ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
    return ret?10:20;
#endif
}
