/**************************************************************************************************

Solver.h -- (C) Niklas Een, Niklas S�rensson, 2004

A simple Chaff-like SAT-solver with support for incremental SAT.

**************************************************************************************************/

#ifndef SatELite_h
#define SatELite_h

#include "Int.h"
#include "SolverTypes.h"
#include "VarOrder.h"

namespace MiniSatPP {

namespace SatELite {

#ifndef __SGI_STL_INTERNAL_RELOPS   // (be aware of SGI's STL implementation...)
#define __SGI_STL_INTERNAL_RELOPS
template <class T> macro bool operator != (const T& x, const T& y) { return !(x == y); }
template <class T> macro bool operator >  (const T& x, const T& y) { return y < x;     }
template <class T> macro bool operator <= (const T& x, const T& y) { return !(y < x);  }
template <class T> macro bool operator >= (const T& x, const T& y) { return !(x < y);  }
#endif

extern bool opt_confl_1sub  ;
extern bool opt_confl_ksub  ;
extern bool opt_var_elim    ;
extern bool opt_0sub        ;
extern bool opt_1sub        ;
extern bool opt_2sub        ;
extern bool opt_repeated_sub;
extern bool opt_def_elim    ;
extern bool opt_unit_def    ;
extern bool opt_hyper1_res  ;
extern bool opt_pure_literal;
extern bool opt_asym_branch ;
extern bool opt_keep_all    ;
extern bool opt_no_random   ;
extern bool opt_pre_sat     ;
extern bool opt_ext_sat     ;
extern bool opt_niver       ;
extern cchar* input_file    ;
extern cchar* output_file   ;
extern cchar* varmap_file   ;
extern cchar* elimed_file   ;
extern cchar* model_file    ;

//#################################################################################################
// INLINED "Queue.h" HERE:
template <class T>
class Queue {
    vec<T>  elems;
    int     first;
public:
    Queue(void) : first(0) { }
    void insert(T x)   { elems.push(x); }
    T    dequeue(void) { return elems[first++]; }
    void clear(void)   { elems.clear(); first = 0; }
    int  size(void)    { return elems.size() - first; }
    bool has(T x) { for (int i = first; i < elems.size(); i++) if (elems[i] == x) return true; return false; }
};
//#################################################################################################


//#################################################################################################
// INLINED "TmpFiles.h" HERE:
FILE* createTmpFile(cchar* prefix, cchar* mode, char*& out_name = *(char**)NULL);
void  deleteTmpFile(cchar* prefix, bool exact = false);
void  deleteTmpFiles(void);
//#################################################################################################


#define BUMP_MORE


//=================================================================================================
// Clause:


class Solver;

struct Clause_t {
    int     id_;        // -1 = dynamic clause
    union {
        struct {
            uint64  abst_;
            uint    size_learnt;
        } A;
        struct {
            char    _vec[sizeof(vec<Lit>)];
        } B;
    } U;
    Lit     data[1];

    vec<Lit>&   Vec(void) const { return *((vec<Lit>*)&U.B._vec); }

    // PUBLIC INTERFACE:
    //
    bool       dynamic     (void)      const { return id_ == -1; }
    int        size        (void)      const { return dynamic() ? Vec().size() : U.A.size_learnt >> 1;}
    Lit&       operator [] (int index)       { return dynamic() ? Vec()[index] : data[index]; }
    const Lit& operator [] (int index) const { return dynamic() ? Vec()[index] : data[index]; }
    Lit&       operator () (int index)       { assert(!dynamic()); return data[index]; }
    const Lit& operator () (int index) const { assert(!dynamic()); return data[index]; }
    void       push        (Lit p)           { assert(dynamic()); Vec().push(p); }
    void       clear       (void)            { assert(dynamic()); Vec().clear(); }
    vec<Lit>&  asVec       (void)      const { assert(dynamic()); return Vec(); }

    // Constructors:
    Clause_t(void) { id_ = -1; new (&Vec()) vec<Lit>(); }
   ~Clause_t(void) { assert(dynamic()); Vec().~vec<Lit>(); }
};


class Clause {
    Clause_t* ptr_;
public:
    Clause(void)        : ptr_(NULL) {}
    Clause(Clause_t& c) : ptr_(&c) {}
    Clause(Clause_t* c) : ptr_( c) {}
    Clause_t* ptr(void) const { return ptr_; }

    bool    operator == (Clause other)  const { return ptr_ == other.ptr_; }
    bool    null(void)                  const { return ptr_ == NULL; }
    void    zero(void)                        { ptr_ = NULL; }

    bool       dynamic     (void)       const { return ptr_->dynamic(); }
    int        size        (void)       const { return ptr_->size(); }
    Lit&       operator [] (int index)        { return (*ptr_)[index]; }
    const Lit& operator [] (int index)  const { return (*ptr_)[index]; }
    Lit&       operator () (int index)        { return (*ptr_)(index); }
    const Lit& operator () (int index)  const { return (*ptr_)(index); }

    // Dynamic:
    void       push        (Lit p)      const { return ptr_->push(p); }
    void       clear       (void)       const { return ptr_->clear(); }
    vec<Lit>&  asVec       (void)       const { return ptr_->asVec(); }

    // Non-dynamic:
    int        id          (void)       const { assert(!dynamic()); return ptr_->id_; }
    uint64     abst        (void)       const { assert(!dynamic()); return ptr_->U.A.abst_; }
    bool       learnt      (void)       const { assert(!dynamic()); return ptr_->U.A.size_learnt & 1; }
    float&     activity    (void)       const { assert(learnt()); return *((float*)&ptr_->data[size()]); }   // (learnt clauses only)
};

const Clause Clause_NULL = Clause();

macro bool operator < (Clause c1, Clause c2) { return (intp)c1.ptr() < (intp)c2.ptr(); }
macro uint hash(Clause c) { return (int)c.id(); }



//=================================================================================================
// Clause Subset:


class CSet {
    vec<int>    where;  // Map clause ID to position in 'which'.
    vec<Clause> which;  // List of clauses (for fast iteration). May contain 'Clause_NULL'.
    vec<int>    free;   // List of positions holding 'Clause_NULL'.

public:
    Clause  operator [] (int index) const { return which[index]; }
    int     size        (void)      const { return which.size(); }
    int     nElems      (void)      const { return which.size() - free.size(); }

    bool    add(Clause c) {
        assert(!c.null());
        where.growTo(c.id()+1, -1);
        if (where[c.id()] != -1)
            return true;
        if (free.size() > 0){
            where[c.id()] = free.last();
            which[free.last()] = c;
            free.pop();
        }else{
            where[c.id()] = which.size();
            which.push(c);
        }
        return false;
    }

    bool    exclude(Clause c) {
        assert(!c.null());
        if (c.id() >= where.size() || where[c.id()] == -1)
            return false;
        free.push(where[c.id()]);
        which[where[c.id()]] = Clause_NULL;
        where[c.id()] = -1;
        return true;
    }

    void    clear(void) {
        for (int i = 0; i < which.size(); i++)
            if (!which[i].null())
                where[which[i].id()] = -1;
        which.clear();
        free .clear();
    }
};



//=================================================================================================
// Helpers:


template <class T>
macro void remove(vec<T>& ws, const T& elem)
{
    int j = 0;
    for (; ws[j] != elem  ; j++) assert(j < ws.size());
    for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
    ws.pop();
}

template <class T> macro void maybeRemove(vec<T>& ws, const T& elem) { if (ws.size() > 0) remove(ws, elem); }


macro int find(Clause c, Lit p) {
    for (int i = 0;; i++){
        assert(i < c.size());
        if (c[i] == p) return i; } }

template <class T>
macro int find(const vec<T>& ws, const T& elem) {   // 'find' has pre-condition that the element exists in the vector.
    for (int i = 0;; i++){
        assert(i < ws.size());
        if (ws[i] == elem) return i; } }


//=================================================================================================
// Solver -- the main class:


struct SolverStats : public BasicSolverStats {
    int64   reduceDBs;
    SolverStats(void) : reduceDBs(0) {}
};


struct SearchParams {
    double  var_decay, clause_decay, random_var_freq;    // (reasonable values are: 0.95, 0.999, 0.02)
    bool    simplify;
    SearchParams(double v = 1, double c = 1, double r = 0, bool s = true) : var_decay(v), clause_decay(c), random_var_freq(r), simplify(s) {}
};

enum OccurMode { occ_Off, occ_Permanent, occ_All };


struct Solver {

// INTERNAL

    bool                ok;             // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<Clause>         constrs;        // Set of problem clauses.
    vec<int>            constrs_free;   // Free list for problem clauses.
    vec<Clause>         learnts;        // Set of learnt clauses.
    vec<int>            learnts_free;   // Free list for learnt clauses.
    double              cla_inc;        // Amount to bump next clause with.
    double              cla_decay;      // INVERSE decay factor for clause activity: stores 1/decay.
    int                 n_literals;     // Literal count -- for output mainly. Only includes *problem* clauses.
    FILE*               elim_out;       // File storing eliminated clauses (needed to calculate model).
    char*               elim_out_file;  // (name of file)
    vec<vec<Clause>*>   iter_vecs;      // Vectors currently used for iterations. Removed clauses will be looked up and replaced by 'Clause_NULL'.
    vec<CSet*>          iter_sets;      // Sets currently used for iterations.

    vec<double>         activity;       // A heuristic measurement of the activity of a variable.
    vec<char>           polarity_sug;   // Suggestion (from user of Solver) for initial polarity to branch on. An 'lbool' coded as a 'char'.
    double              var_inc;        // Amount to bump next variable with.
    double              var_decay;      // INVERSE decay factor for variable activity: stores 1/decay. Use negative value for static variable order.
  #ifdef VAR_ORDER_2
    vec<double>         lt_activity;    // Long term activity.
    VarOrder2           order;          // Keeps track of the decision variable order.
  #else
    VarOrder            order;          // Keeps track of the decision variable order.
  #endif

    vec<vec<Clause> >   watches;        // 'watches[index(lit)]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    bool                watches_setup;  // Are the watcher lists set up yet? ('false' initially)
    vec<vec<Clause> >   occur;          // 'occur[index(lit)]' is a list of constraints containing 'lit'.
    OccurMode           occur_mode;     // What clauses to keep in the occur lists.
    vec<int>            n_occurs;       // Literal occurance count -- only for problem clauses. Used for pure-literal rule.
    Queue<Lit>          propQ;          // Propagation queue.

    vec<int>            assigns;        // The current assignments (lbool:s stored as char:s).
    vec<Lit>            units;          // ... the other solution to 'persistent'; re-propagate when reach toplevel.
    vec<Lit>            trail;          // List of assignments made.
    vec<int>            trail_lim;      // Separator indices for different decision levels in 'trail'.
    vec<Clause>         reason;         // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
    vec<int>            level;          // 'level[var]' is the decision level at which assignment was made.
    int                 root_level;     // Level of first proper decision.
    int                 last_simplify;  // Number of top-level assignments at last 'simplifyDB()'.

    vec<char>           touched;        // Is set to true when a variable is part of a removed clause. Also true initially (upon variable creation).
    vec<Var>            touched_list;   // A list of the true elements in 'touched'.
    CSet                cl_touched;     // Clauses strengthened.
    CSet                cl_added;       // Clauses created.
    bool                fwd_subsump;    // Forward subsumption activated?

    vec<char>           var_elimed;     // 'eliminated[var]' is TRUE if variable has been eliminated.
    vec<char>           frozen;         // Variables currently not to be subjected for elimination.

    int64               last_inspects;  // Number of inspects since last removal of satified clauses in 'simplifyDB()' -- to avoid doing it too often.

    // Temporaries (to reduce allocation overhead):
    //
    vec<char>           seen_tmp;       // (used in various places)
    vec<char>           touched_tmp;    // (used in 'simplifyBySubsumption()' to mark variables touched during elimination)
    vec<Lit>            unit_tmp;       // (used in 'addUnit()')
    vec<Lit>            io_tmp;         // (used for reading/writing clauses from/to disk)

    // Main internal methods:
    //
    void    analyze          (Clause confl, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
    bool    enqueue          (Lit fact, Clause from = NULL);
    Clause  propagate        (void);
    void    propagateToplevel(void);
    void    reduceDB         (void);
    void    compressDB       (void);
    Lit     pickBranchLit    (const SearchParams& params);
    lbool   search           (int nof_conflicts, int nof_learnts, const SearchParams& params);
    double  progressEstimate (void);
    void    extendModel      (void);

    // Clauses:
    //
    Clause  allocClause     (const vec<Lit>& ps, bool learnt, Clause overwrite = Clause_NULL);
    void    deallocClause   (Clause c, bool quick = false);
    void    unlinkClause    (Clause c, Var elim = var_Undef);
    bool    propagateClause (Clause c, Lit p, bool& keep_watch);
    void    calcReason      (Clause c, Lit p, vec<Lit>& out_reason);
    void    strengthenClause(Clause c, Lit p);

    // Other database management:
    //
    void    createTmpFiles(cchar* filename) {
        if (filename == NULL)
            elim_out = createTmpFile("/tmp/tmp_elims__", "w+b", elim_out_file);
        else
            elim_out = fopen(filename, "w+b"),
            elim_out_file = NULL; }
    void    deleteTmpFiles(void) { if (elim_out_file != NULL) deleteTmpFile(elim_out_file, true); }
    void    registerIteration  (vec<Clause>& iter_vec) { iter_vecs.push(&iter_vec); }
    void    unregisterIteration(vec<Clause>& iter_vec) { remove(iter_vecs, &iter_vec); }
    void    registerIteration  (CSet&        iter_set) { iter_sets.push(&iter_set); }
    void    unregisterIteration(CSet&        iter_set) { remove(iter_sets, &iter_set); }
    void    setOccurMode(OccurMode occur_mode);
    void    setupWatches(void);

    // Activity:
    //
    void    varBumpActivity(Lit p) {
        if (var_decay < 0) return;     // (negative decay means static variable order -- don't bump)
        if ( (activity[var(p)] += var_inc) > 1e100 ) varRescaleActivity();
      #ifdef VAR_ORDER_2
        lt_activity[var(p)] += 1.0;
      #endif
        order.update(var(p)); }
    void    varDecayActivity(void) { if (var_decay >= 0) var_inc *= var_decay; }
    void    varRescaleActivity(void);

    void    claBumpActivity(Clause c) { if ( (c.activity() += cla_inc) > 1e20 ) claRescaleActivity(); }
    void    claDecayActivity(void) { cla_inc *= cla_decay; }
    void    claRescaleActivity(void);

    // Helpers:
    //
    bool    assume       (Lit p);
    void    undoOne      (void);
    void    cancel       (void);
    void    cancelUntil  (int level);
    void    record       (const vec<Lit>& clause);
    bool    locked       (Clause c) { return reason[var(c[0])] == c; }
    int     decisionLevel(void) { return trail_lim.size(); }

    void    watch        (Clause c, Lit p) { watches[index(p)].push(c); }
    void    unwatch      (Clause c, Lit p) { remove(watches[index(p)], c); }

    int     allocClauseId(bool learnt);
    void    freeClauseId (int id, bool learnt);


// PUBLIC INTERFACE

    Solver(OccurMode mode = occ_Permanent, cchar* elimed_filename = NULL)
                 : ok               (true)
                 , cla_inc          (1)
                 , cla_decay        (1)
                 , n_literals       (0)
                 , var_inc          (1)
                 , var_decay        (1)
               #ifdef VAR_ORDER_2
                 , order            (assigns, activity, lt_activity, var_inc)
               #else
                 , order            (assigns, activity)
               #endif
                 , watches_setup    (false)
                 , occur_mode       (mode)
                 , root_level       (0)
                 , last_simplify    (-1)
                 , fwd_subsump      (false)
                 , last_inspects    (0)
                 , unit_tmp         (1, lit_Undef)
                 , progress_estimate(0)
                 , verbosity(0)
                 { createTmpFiles(elimed_filename);
                #ifndef WATCH_OPTIMIZATION
                   watches_setup = true;
                #endif
                 }
   ~Solver(void);

    // Helpers: (semi-internal)
    //
    lbool   value(Var x) { return toLbool(assigns[x]); }
    lbool   value(Lit p) { return sign(p) ? ~toLbool(assigns[var(p)]) : toLbool(assigns[var(p)]); }

    int     nAssigns (void) { return trail.size(); }
    int     nLiterals(void) { return n_literals; }
    int     nClauses (void) { return constrs.size() - constrs_free.size(); }
    int     nLearnts (void) { return learnts.size() - learnts_free.size(); }

    // Statistics: (read-only member variable)
    //
    SolverStats stats;
    int		numOfClouses (void)  {  return constrs.size()+ learnts.size(); }

    // Problem specification:
    //
    Var     newVar (bool decision_var = true);
    int     nVars  (void)  { return assigns.size(); }
    void    addUnit(Lit p) { assert(unit_tmp.size() == 1); unit_tmp[0] = p; addClause(unit_tmp); }

    // -- constraints:
    Clause  addClause(const vec<Lit>& ps, bool learnt = false, Clause overwrite = Clause_NULL);
    void    removeClause(Clause c, Var elim = var_Undef) { if (ok) { unlinkClause(c, elim); deallocClause(c); } }

    void    freeze(Var x) { frozen[x] = 1; }
    void    thaw  (Var x) { frozen[x] = 0; }

    // Solving:
    //
    bool    okay(void) { return ok; }
    void    simplifyDB(bool subsume = false);
    bool    solve(const vec<Lit>& assumps);
    bool    solve(void) { vec<Lit> empty; return solve(empty); }

    double      progress_estimate;  // Set by 'search()'.
    vec<lbool>  model;              // If problem is solved, this vector contains the model (if any).
    int         verbosity;          // Verbosity level. 0=silent, 1=some progress report, 2=everything

    // Subsumption:
    //
    void touch(Var x) { if (!touched[x]) touched[x] = 1, touched_list.push(x); }
    void touch(Lit p) { touch(var(p)); }
    bool updateOccur(Clause c) { return occur_mode == occ_All || (occur_mode == occ_Permanent && !c.learnt()); }

    int  literalCount(void);        // (just progress measure)
    void findSubsumed(Clause ps, vec<Clause>& out_subsumed);
    bool isSubsumed(Clause ps);
    bool hasClause(Clause ps);
    void subsume0(Clause ps, int& counter = *(int*)NULL);
    void subsume1(Clause ps, int& counter = *(int*)NULL);
    void simplifyBySubsumption(bool with_var_elim = true);

    void orderVarsForElim(vec<Var>& order);
    int  substitute(Lit x, Clause def, vec<Clause>& poss, vec<Clause>& negs, vec<Clause>& new_clauses);
    Lit  findUnitDef(Var x, vec<Clause>& poss, vec<Clause>& negs);
    bool findDef(Lit x, vec<Clause>& poss, vec<Clause>& negs, Clause out_def);
    bool maybeEliminate(Var x);

    void checkConsistency(void);

    void clauseReduction(void);
    void asymmetricBranching(Lit p);

};


//=================================================================================================
// Debug:


// For derivation output (verbosity level 2)
#define L_IND    "%-*d"
#define L_ind    decisionLevel()*3+3,decisionLevel()
#define L_LIT    "%sx%d"
#define L_lit(p) sign(p)?"~":"", var(p)

// Just like 'assert()' but expression will be evaluated in the release version as well.
#ifdef NDEBUG
  inline void check(bool expr) { assert(expr); }
#else
  #define check assert
#endif


macro void dump(Clause c, bool newline = true, FILE* out = stdout) {
    fprintf(out, "{");
//    for (int i = 0; i < c.size(); i++) fprintf(out, " "L_LIT, L_lit(c[i]));
    fprintf(out, " }%s", newline ? "\n" : "");
    fflush(out);
}
macro void dump(Solver& S, Clause c, bool newline = true, FILE* out = stdout) {
    fprintf(out, "{");
 //   for (int i = 0; i < c.size(); i++) fprintf(out, " "L_LIT":%c", L_lit(c[i]), name(S.value(c[i])));
    fprintf(out, " }%s", newline ? "\n" : "");
    fflush(out);
}

macro void dump(const vec<Lit>& c, bool newline = true, FILE* out = stdout) {
    fprintf(out, "{");
 //   for (int i = 0; i < c.size(); i++) fprintf(out, " "L_LIT, L_lit(c[i]));
    fprintf(out, " }%s", newline ? "\n" : "");
    fflush(out);
}
macro void dump(Solver& S, vec<Lit>& c, bool newline = true, FILE* out = stdout) {
    fprintf(out, "{");
 //   for (int i = 0; i < c.size(); i++) fprintf(out, " "L_LIT":%c", L_lit(c[i]), name(S.value(c[i])));
    fprintf(out, " }%s", newline ? "\n" : "");
    fflush(out);
}


//=================================================================================================
}

}
#endif
