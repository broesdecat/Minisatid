#include <ctime>
#include <cstring>
#include <stdint.h>
#include <errno.h>

#include <cmath> // for "pow"

#include <signal.h>
#include <zlib.h>

#include "Solver.h"
#include "TSolver.h"

/*************************************************************************************/
#if defined(__linux__)
static inline int memReadStat(int field)
{
    char    name[256];
    pid_t pid = getpid();
    sprintf(name, "/proc/%d/statm", pid);
    FILE*   in = fopen(name, "rb");
    if (in == NULL) return 0;
    int     value;
    for (; field >= 0; field--)
        fscanf(in, "%d", &value);
    fclose(in);
    return value;
}
static inline uint64_t memUsed() { return (uint64_t)memReadStat(0) * (uint64_t)getpagesize(); }
#elif defined(__FreeBSD__)
static inline uint64_t memUsed(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss*1024; }
#else
static inline uint64_t memUsed() { return 0; }
#endif

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
static void readClause(B& in, Solver* S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S->nVars()) S->newVar();
        S->setDecisionVar(var,true); // S.nVars()-1   or   var
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
template<class B>
static void parse_Aggr(B& in, Solver* S, TSolver* TS, AggrType type) {
    int defn = parseInt(in);
    if (defn<=0)
        ParseError("Defining literal of aggregate expression has to be an atom (found %d).\n",defn);
    else defn--;
    while (defn >= S->nVars()) S->newVar();
    S->setDecisionVar(defn,true);
    int set_id = parseInt(in);
    int min = parseInt(in);
    int max = parseInt(in);
    int zero = parseInt(in);
    if (zero != 0)
        ParseError("Aggregate expression has to be closed with '0' (found %d).\n",zero);
    TS->addAggrExpr(defn,set_id,min,max,type);
}
/////////END OF EXTENSIONS


template<class B>
static void parse_ECNF_main(B& in, Solver* S, TSolver* TS) { // NOTE: this parser does not read translation information.
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
//////////////////START OF EXTENSIONS
				case 'C':
                    if (match(in,"Card"))
                        parse_Aggr(in, S, TS, SUM); // NOTE: weights =1 are automatically added.
                    else { // conjunctive rule.
                        ++in;
                        readClause(in, S, lits);
                        TS->addRule(true, lits);
                    }
                    break;
                case 'D': // disjunctive rule.
                    ++in;
                    readClause(in, S, lits);
                    TS->addRule(false, lits);
                    break;
                case 'E':
                    if (match(in,"EU")) {
                        readClause(in, S, lits);
                        TS->addAMO(lits); // First this, because S.addClause(lits) empties lits.
                        S->addClause(lits);
                        //Clause * cl;
                        //S.addClause(lits,cl); // TODO
                        //S.addAMO(lits,cl);
                    } else
                        ParseError("Unexpected char '%c' after 'E' (expecting \"EU\").\n",*in);
                    break;
                case 'A':
                    if (match(in,"AMO")) {
                        readClause(in, S, lits);
                        TS->addAMO(lits); // TODO
                    } else
                        ParseError("Unexpected char '%c' after 'A' (expecting \"AMO\").\n",*in);
                    break;
                case 'M':
                    ++in;
                    if (*in == 'i' && match(in,"in"))
                        parse_Aggr(in, S, TS, MIN);
                    else if (*in == 'a' && match(in,"ax"))
                        parse_Aggr(in, S, TS, MAX);
                    /*else if (*in == 'n' && match(in,"nmz")) {
                        readClause(in, S, lits);
                        TS->Subsetminimize(lits);
                    }*/ else
                        ParseError("Unexpected char '%c' after 'M' (expecting \"Min\", \"Max\" or \"Mnmz\").\n",*in);
                    break;
                case 'P':
                    if (match(in,"Prod"))
                        parse_Aggr(in, S, TS, PROD);
                    else
                        ParseError("Unexpected char '%c' after 'P' (expecting \"Prod\").\n",*in);
                    break;
                case 'S':
                    ++in;
                    if (*in == 'e' && match(in,"et")) {
                        int set_id = parseInt(in); // Note that set_id 0 cannot exist.
                        readClause(in, S, lits);
                        vec<int> w(lits.size(),1); // Treat CARD as SUM with all weights =1.
                        TS->addSet(set_id,lits,w);
                    } else if (*in == 'u' && match(in,"um"))
                        parse_Aggr(in, S, TS, SUM);
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
                            while (var >= S->nVars()) S->newVar();
                            S->setDecisionVar(var,true); // S.nVars()-1   or   var
                            lits.push( (parsed_lit > 0) ? Lit(var) : ~Lit(var) );
                            if (*in != '=')
                                ParseError("Encountered weightless literal in \"WSet\" declaration.\n");
                            ++in;
                            parsed_lit = parseInt(in);
                            weights.push(parsed_lit);
                        }
                        TS->addSet(set_id,lits,weights);
                    } else
                        ParseError("Unexpected char '%c' after 'W' (expecting \"WSet\").\n",*in);
                    break;
//////////////////END OF EXTENSIONS
                default:
                    readClause(in, S, lits);
                    S->addClause(lits);
                    break;
            }
        }
    }
//////////////////START OF EXTENSIONS
    TS->finishECNF_DataStructures();
//////////////////END OF EXTENSIONS
}

template<class B>
static void parse_main(B& in, Solver* S, TSolver* TS) {
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
                if (S->verbosity>=1) {
                    reportf("|  Number of variables:  %-12d                                         |\n", vars);
                    reportf("|  Number of clauses:    %-12d                                         |\n", clauses);
                }
                ecnf=true;
                break;
            }else if (match(in,"ecnf")) {
                ecnf=true;
                if (S->verbosity>=1)
                    reportf("| Reading ECNF file.                                                          |\n");
                for (;*in!='\n';) {
                    while (*in == 9 || *in == 11 || *in == 12 || *in == 13 || *in == 32) ++in;
                    if (*in==EOF || *in=='\0' || *in=='\n') break;
                    if (*in=='d' && match(in,"def")) {
                        if (S->verbosity>=1)
                            reportf("|    May contain inductive definitions.                                       |\n");
                        TS->ecnf_mode.def=true;
                    } else if (*in=='e' && match(in,"eu")) {
                        if (S->verbosity>=1)
                            reportf("|    May contain exists unique statements (registered as at-most-one).        |\n");
                        TS->ecnf_mode.amo=true;
                    } else if (*in=='a') {
                        ++in;
                        if (*in=='m' && match(in,"mo")) {
                            if (S->verbosity>=1)
                                reportf("|    May contain at most one statements                                  |\n");
                            TS->ecnf_mode.amo=true;
                        } else if (*in=='g' && match(in,"ggr")) {
                            if (S->verbosity>=1)
                                reportf("|    May contain aggregate expressions.                                       |\n");
                            TS->ecnf_mode.aggr=true;
                        } else
                            ParseError("Unexpected ECNF extension type (known: \"def\", \"eu\", \"amo\", \"aggr\"); stuck on '%c'.\n",*in);
                    } else if (*in=='m' && match(in,"mnmz")) {
                        if (S->verbosity>=1)
                            reportf("|    May contain an optimize statement.                                       |\n");
                        TS->ecnf_mode.mnmz=true;
                    } else
                        ParseError("Unexpected ECNF extension type (known: \"def\", \"eu\", \"amo\", \"aggr\"); stuck on '%c'.\n",*in);
                }
                ++in;
                break;
            }else
                ParseError("Unexpected char: %c\n", *in);
        } else if (*in == 'c' || *in == 'p') {
            if (match(in, "c grounder error"))
                reportf("There was a grounding error; MiniSat can't continue solving.\n"), exit(1);
            else
                skipLine(in);
        } else
            ParseError("Unexpected char: %c\n", *in);
    }
    if (ecnf){
    	parse_ECNF_main(in, S, TS);
    }else{
    	reportf("Format no longer supported.\n"), exit(1);
    }
}

// Inserts problem into solver.
//
static void parse(gzFile input_stream, Solver* S, TSolver* TS) {
    StreamBuffer in(input_stream);
    parse_main(in, S, TS); }

//=================================================================================================


void printStats(Solver* solver) // TODO stats for aggr, eu.
{
	//TODO repair later
    /*if (solver.verbosity>=1) {
        double cpu_time = cpuTime();
        uint64_t mem_used = memUsed();
        reportf("restarts              : %lld\n", solver.starts);
        reportf("conflicts             : %-12lld   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
        reportf("decisions             : %-12lld   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
        reportf("propagations          : %-12lld   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
        reportf("conflict literals     : %-12lld   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
        if (mem_used != 0) reportf("Memory used           : %.2f MB\n", mem_used / 1048576.0);
        reportf("CPU time              : %g s\n", cpu_time);
        if (solver.ecnf_mode.def) {
            reportf("cycles                : %-12lld   (%4.2f /decision)\n", solver.cycles, (float)solver.cycles/solver.decisions);
            reportf("cycle conflicts       : %-12lld\n", solver.justify_conflicts);
            reportf("avg cycle size        : %4.2f\n", (float)solver.cycle_sizes/solver.cycles);
            reportf("avg extdisj size      : %4.2f\n", (float)solver.extdisj_sizes/solver.cycles);
            reportf("justify runs          : %-12lld   (%4.2f /cycle)\n", solver.justify_calls, (float)solver.justify_calls/solver.cycles);
            reportf("avg. justify searchsp.: %6.2f lits\n", (float)solver.total_marked_size/solver.justify_calls);
            reportf("cycle sources         : %-12lld   (%4.2f /decision)\n", solver.cycle_sources, (float)solver.cycle_sources/solver.decisions);
            reportf("                      : %4.2f found per run of findCycleSources()\n", (float)solver.nb_times_findCS/solver.cycle_sources);
            reportf("                      : %4.2f removed per justify run\n", (float)solver.cs_removed_in_justify/solver.justify_calls);
            reportf("                      : %4.2f treated per loop\n", (float)solver.succesful_justify_calls/solver.nb_times_findCS);
//            reportf("                      : %lld fw propagations, out of %lld attempts, succes %6.4f%%",solver.fw_propagations,solver.fw_propagation_attempts,(float)solver.fw_propagations/solver.fw_propagation_attempts);
        }
        reportf("\n");
    }*/
}

Solver* solver;
static void SIGINT_handler(int signum) {
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    printStats(solver);
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    exit(1);
}


//=================================================================================================
// Main:

void printUsage(char** argv)
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


const char* hasPrefix(const char* str, const char* prefix)
{
    int len = strlen(prefix);
    if (strncmp(str, prefix, len) == 0)
        return str + len;
    else
        return NULL;
}


int main(int argc, char** argv)
{
    Solver*      S = new Solver();
    TSolver* 	TS = new TSolver();
    S->setTSolver(TS);
    TS->setSolver(S);
    //S->verbosity = 1;

    int         i, j;
    int         N = 1;
    const char* value;
    for (i = j = 0; i < argc; i++){
        if ((value = hasPrefix(argv[i], "-polarity-mode="))){
            if (strcmp(value, "true") == 0)
               S->polarity_mode = Solver::polarity_true;
            else if (strcmp(value, "false") == 0)
               S->polarity_mode = Solver::polarity_false;
            else if (strcmp(value, "rnd") == 0)
               S->polarity_mode = Solver::polarity_rnd;
            else{
                reportf("ERROR! unknown polarity-mode %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-defn_strategy="))){
            if (strcmp(value, "always") == 0)
                TS->defn_strategy = TSolver::always;
            else if (strcmp(value, "adaptive") == 0)
                TS->defn_strategy = TSolver::adaptive;
            else if (strcmp(value, "lazy") == 0)
                TS->defn_strategy = TSolver::lazy;
            else{
                reportf("ERROR! illegal definition strategy %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-defn_search="))){
            if (strcmp(value, "include_cs") == 0)
                TS->defn_search = TSolver::include_cs;
            else if (strcmp(value, "stop_at_cs") == 0)
                TS->defn_search = TSolver::stop_at_cs;
            else{
                reportf("ERROR! illegal definition ssearch type %s\n", value);
                exit(0); }

        }else if ((value = hasPrefix(argv[i], "-rnd-freq="))){
            double rnd;
            if (sscanf(value, "%lf", &rnd) <= 0 || rnd < 0 || rnd > 1){
                reportf("ERROR! illegal rnd-freq constant %s\n", value);
                exit(0); }
            S->random_var_freq = rnd;

        }else if ((value = hasPrefix(argv[i], "-decay="))){
            double decay;
            if (sscanf(value, "%lf", &decay) <= 0 || decay <= 0 || decay > 1){
                reportf("ERROR! illegal decay constant %s\n", value);
                exit(0); }
           S->var_decay = 1 / decay;

        }else if ((value = hasPrefix(argv[i], "-verbosity="))){
            int verbosity = (int)strtol(value, NULL, 10);
            if (verbosity == 0 && errno == EINVAL){
                reportf("ERROR! illegal verbosity level %s\n", value);
                exit(0); }
           S->verbosity = verbosity;
            TS->verbosity = verbosity;

        }else if ((value = hasPrefix(argv[i], "-maxruntime="))){
           S->maxruntime = (double)strtol(value, NULL, 10);
            if (S->maxruntime <= 0.0) {
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


    if (S->verbosity>=1)
        reportf("This is MiniSat 2.0 beta\n");
#if defined(__linux__)
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
    if (S->verbosity>=1)
        reportf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
    double cpu_time = cpuTime();

    solver = S;
    signal(SIGINT,SIGINT_handler);
    signal(SIGHUP,SIGINT_handler);

    if (argc == 1)
        reportf("Reading from standard input... Use '-h' or '--help' for help.\n");

    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        reportf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

    if (S->verbosity>=1) {
        reportf("============================[ Problem Statistics ]=============================\n");
        reportf("|                                                                             |\n");
    }

    parse(in, S, TS);
    gzclose(in);
    FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

    if (S->verbosity>=1) {
        double parse_time = cpuTime() - cpu_time;
        reportf("| Parsing time              : %7.2f s                                       |\n", parse_time);
    }

    if (!S->simplify()){
        if (S->verbosity>=1) {
            reportf("===============================================================================\n");
            reportf("Solved by unit propagation\n");
        }
        if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
        printf("UNSATISFIABLE\n");
        exit(20);
    }

    S->nb_models=N;
    S->res=res;
    bool ret = S->solve();
    printStats(S);

    delete TS;

#ifdef NDEBUG
    exit(ret ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
    return ret?10:20;
#endif
}
