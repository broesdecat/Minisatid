/****************************************************************************************[Solver.h]
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

#ifndef Solver_h
#define Solver_h

#include <cstdio>
#include <set>
#include <map>

#include "Vec.h"
#include "Queue.h"
#include "Heap.h"
#include "Alg.h"

#include "solverfwd.h"
#include "debug.h"

#include "IDSolver.h"
#include "AggSolver.h"

class IDSolver;
class AggSolver;
class Solver;
typedef shared_ptr<IDSolver> pIDSolver;
typedef weak_ptr<IDSolver> wpIDSolver;
typedef shared_ptr<AggSolver> pAggSolver;
typedef weak_ptr<AggSolver> wpAggSolver;
typedef shared_ptr<Solver> pSolver;
typedef weak_ptr<Solver> wpSolver;

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

//=================================================================================================
// Solver -- the main class:

class Solver {
private:
	//this class is the owner, to allow most efficiency
	pIDSolver 	tsolver;
	pAggSolver	aggsolver;

public:
	/////SMT NECESSARY
	void 				setIDSolver				(const pIDSolver& s)	{ tsolver = s; }
	void 				resetIDSolver			() 						{ tsolver.reset();}
	void 				setAggSolver			(const pAggSolver& s)	{ aggsolver = s; }
	void 				resetAggSolver			()						{ aggsolver.reset(); }
	const pIDSolver& 	getIDSolver				()				const 	{ return tsolver; }
	const pAggSolver& 	getAggSolver			()				const 	{ return aggsolver; }

	lbool   value      (Var x) const;       // The current value of a variable.
	lbool   value      (Lit p) const;       // The current value of a literal.
	int     nVars      ()      const;       // The current number of variables.

    //VERY VERY IMPORTANT: THE FIRST LITERAL IN THE CLAUSE HAS TO BE THE ONE WHICH CAN BE PROPAGATED FROM THE REST!!!!!!!
    void 	addLearnedClause(Clause* c);	// don't check anything, just add it to the clauses and bump activity
    bool    addClause		(vec<Lit>& ps);	// Add a clause to the solver. NOTE! 'ps' may be shrunk by this method!
    void    backtrackTo		(int level);	// Backtrack until a certain level.
    void    setTrue			(Lit p, Clause* from = NULL);				// Enqueue a literal. Assumes value of literal is undefined
    Var		newVar			(bool polarity = true, bool dvar = false);	// Add a new variable with parameters specifying variable mode.
	/////END SMT NECESSARY

	/////////////////////TSOLVER NECESSARY
    /*
     * Returns the decision level at which a variable was deduced. This allows to get the variable that was propagated earliest/latest
     */
	int 	getLevel(int var) 			const;

	/**
	 * Allows to loop over all assignments made in the current decision level.
	 */
	Lit 	getRecentAssignments(int i) const;
	int 	getNbOfRecentAssignments() 	const;

    bool 	existsUnknownVar(); 								//true if the current assignment is completely two-valued
	/////////////////////END TSOLVER NECESSARY

    void finishParsing();

    /*
     * OPTIMIZATION INFORMATION
     */

    MINIM		optim;
    Var 		head;
    vec<Lit>	to_minimize;

    void 	addMinimize(const vec<Lit>& lits, bool subsetmnmz);
    void 	addSumMinimize(const Var head, const int setid);
    bool 	invalidateValue(vec<Lit>& invalidation);
	bool 	invalidateSubset(vec<Lit>& invalidation, vec<Lit>& assmpt);
	bool 	findOptimal(vec<Lit>& assumps, vec<Lit>& m);

	void    invalidateModel(vec<Lit>& invalidation);  // (used if nb_models>1) Add 'lits' as a model-invalidating clause that should never be deleted, backtrack until the given 'qhead' value.
	void 	invalidate(vec<Lit>& invalidation);
	bool 	findNext	(const vec<Lit>& assumpts, vec<Lit>& model);
	bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
	bool    solve		();		// Search for nb_models models without assumptions.
	void 	printModel	();

    // Constructor/Destructor:
    //
	Solver();
    virtual ~Solver();

    // Solving:
    //
    bool    simplify	();		// Removes already satisfied clauses.

    FILE*   res;					// Report results in this file.
    int     nb_models;				// Number of models wanted (all if N=0).
    int		modelsfound;

    // Variable mode:
    //
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    double    var_decay;          // Inverse of the variable activity decay factor.                                            (default 1 / 0.95)
    double    clause_decay;       // Inverse of the clause activity decay factor.                                              (1 / 0.999)
    double    random_var_freq;    // The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
    bool      expensive_ccmin;    // Controls conflict clause minimization.                                                    (default TRUE)
    int       polarity_mode;      // Controls which polarity the decision heuristic chooses. See enum below for allowed modes. (default polarity_false)
    int       verbosity;          // Verbosity level. 0=silent, 1=some progress report
    double    random_seed;        // Used by the random variable selection.

	/* Modified 2009 */
	int restartLess;
	int restartMore;
	float restartTolerance;
	double nof_learnts;
	int* backtrackLevels;
	vec<bool> polarity;

    enum { polarity_true = 0, polarity_false = 1, polarity_stored = 2, polarity_rnd = 3 };

    // Statistics: (read-only member variable)
    //
    uint64_t starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t clauses_literals, learnts_literals, max_literals, tot_literals;

    //Debug
    void     printLit         (Lit l);
    template<class C>
    void     printClause      (const C& c);

protected:
    int			qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
	vec<Lit>	trail;            // Assignment stack; stores all assigments made in the order they were made.

    int     decisionLevel()    const; 		// Gives the current decisionlevel.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    // Helper structures:
    //
    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    friend class VarFilter;
    struct VarFilter {
        const Solver& s;
        VarFilter(const Solver& _s) : s(_s) {}
        bool operator()(Var v) const { return toLbool(s.assigns[v]) == l_Undef && s.decision_var[v]; }
    };

    Clause* propagate        ();								// Perform unit propagation. Returns possibly conflicting clause.

    vec<int>	seen;

    vec<int>	trail_lim;        // Separator indices for different decision levels in 'trail'.
    bool		ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    bool		remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    vec<int>	level;            // 'level[var]' contains the level at which the assignment was made.


    // Solver state:
    //
    vec<Clause*>        clauses;          // List of problem clauses.
    vec<Clause*>        learnts;          // List of learnt clauses.
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    vec<vec<Clause*> >  watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<char>           assigns;          // The current assignments (lbool:s stored as char:s)
    vec<char>           decision_var;     // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Clause*>        reason;           // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;// Set by 'search()'.

    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nAssigns   ()      const;       // The current number of assigned literas.
    int     nLearnts   ()      const;       // The current number of learnt clauses.

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    (int polarity_mode, double random_var_freq);             // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     cancelFurther    (int init_qhead);                                        // Backtrack within level 0 until the given 'qhead' value.
    bool     enqueue          (Lit p, Clause* from = NULL);                            // Test if fact 'p' contradicts current state, enqueue otherwise.
    void     analyze          (Clause* confl, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           ();                    // Search for a given number of conflicts.
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<Clause*>& cs);                                      // Shrink 'cs' to contain only non-satisfied clauses.

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (Clause& c);             // Attach a clause to watcher lists.
    void     detachClause     (Clause& c);             // Detach a clause to watcher lists.
    void     removeClause     (Clause& c);             // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    // Misc:
    //
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...

    // Debug:
    void     verifyModel      ();
    void     checkLiteralCount();

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }
};


//=================================================================================================
// Implementation of inline methods:


inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision_var[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() { var_inc *= var_decay; }
inline void Solver::varBumpActivity(Var v) {
    if ( (activity[v] += var_inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= clause_decay; }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                learnts[i]->activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline bool     Solver::enqueue         (Lit p, Clause* from)   { return value(p) != l_Undef ? value(p) != l_False : (setTrue(p, from), true); }
inline bool     Solver::locked          (const Clause& c) const { return reason[var(c[0])] == &c && value(c[0]) == l_True; }
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level[x] & 31); }
inline lbool    Solver::value         (Var x) const   { return toLbool(assigns[x]); }
inline lbool    Solver::value         (Lit p) const   { return toLbool(assigns[var(p)]) ^ sign(p); }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts.size(); }
inline int      Solver::nVars         ()      const   { return assigns.size(); }
inline void     Solver::setDecisionVar(Var v, bool b) { decision_var[v] = (char)b; if (b) { insertVarOrder(v); } }
inline bool     Solver::okay          ()      const   { return ok; }

inline int		Solver::getLevel(int var)			const	{return level[var];}
inline Lit	 	Solver::getRecentAssignments(int i) const	{return trail[i+trail_lim.last()];}
inline int 		Solver::getNbOfRecentAssignments() 	const	{return trail_lim.size()==0?0:trail.size()-trail_lim.last();}

//=================================================================================================
// Debug + etc:

static inline void logLit(FILE* f, Lit l)
{
    fprintf(f, "%sx%d", sign(l) ? "~" : "", var(l)+1);
}

static inline void logLits(FILE* f, const vec<Lit>& ls)
{
    fprintf(f, "[ ");
    if (ls.size() > 0){
        logLit(f, ls[0]);
        for (int i = 1; i < ls.size(); i++){
            fprintf(f, ", ");
            logLit(f, ls[i]);
        }
    }
    fprintf(f, "] ");
}

static inline const char* showBool(bool b) { return b ? "true" : "false"; }


// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(bool expr) { assert(expr); }


inline void Solver::printLit(Lit l)
{
    reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}


template<class C>
inline void Solver::printClause(const C& c)
{
    for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}


//=================================================================================================
#endif
