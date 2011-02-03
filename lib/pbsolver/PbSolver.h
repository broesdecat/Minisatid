#ifndef PbSolver_h
#define PbSolver_h

#include "Solver.h"
#include "Map.h"
#include "StackAlloc.h"

namespace MiniSatPP {

void printBasesAndTerminate();
SearchMetaData* searchForBase(vec<Int>& inCoeffs, vec<int>& outputBase);

//=================================================================================================
// Linear -- a class for storing pseudo-boolean constraints:


class Linear {
    int     orig_size;  // Allocated terms in constraint.
public:
    int     size;       // Terms in constraint.
    Int     lo, hi;     // Sum should be in interval [lo,hi] (inclusive).
private:
    char    data[1];    // (must be last element of the struct)
public:
    // NOTE: Cannot be used by normal 'new' operator!
    Linear(const vec<Lit>& ps, const vec<Int>& Cs, Int low, Int high) {
        orig_size = size = ps.size(), lo = low, hi = high;
        char* p = data;
        for (int i = 0; i < ps.size(); i++) *(Lit*)p = ps[i], p += sizeof(Lit);
        for (int i = 0; i < Cs.size(); i++) new ((Int*)p) Int(Cs[i]), p += sizeof(Int); }

    Lit operator [] (int i) const { return *(Lit*)(data + sizeof(Lit)*i); }
    Int operator () (int i) const { return *(Int*)(data + sizeof(Lit)*orig_size + sizeof(Int)*i); }
    Lit& operator [] (int i) { return *(Lit*)(data + sizeof(Lit)*i); }
    Int& operator () (int i) { return *(Int*)(data + sizeof(Lit)*orig_size + sizeof(Int)*i); }
};


//=================================================================================================
// PbSolver -- Pseudo-boolean solver (linear boolean constraints):


class PbSolver {
protected:
    Solver              sat_solver;     // Underlying SAT solver.
    bool&               ok;             // True means unsatisfiability has not been detected.
    vec<int>&           assigns;        // Var -> lbool: The current assignments (lbool:s stored as char:s).  ('atype' is 'char' or 'int' depending on solver) 
    vec<Lit>&           trail;          // Chronological assignment stack.

    StackAlloc<char*>   mem;            // Used to allocate the 'Linear' constraints stored in 'constrs' (other 'Linear's, such as the goal function, are allocated with 'xmalloc()')

public:
    vec<Linear*>        constrs;        // Vector with all constraints.
    Linear*             goal;           // Non-normalized goal function (used in optimization). NULL means no goal function specified. NOTE! We are always minimizing.
    int                 formulaSize;
    std::string         status;
	int                 numOfClouses;
	
protected:
    vec<int>            n_occurs;       // Lit -> int: Number of occurrences.
    vec<vec<int> >      occur;          // Lit -> vec<int>: Occur lists. Left empty until 'setupOccurs()' is called.

    int                 propQ_head;     // Head of propagation queue (index into 'trail').


    // Main internal methods:
    //
    bool    propagate(Linear& c);
    void    propagate();
    bool    addUnit  (Lit p) { return sat_solver.addUnit(p); }
    bool    normalizePb(vec<Lit>& ps, vec<Int>& Cs, Int& C,bool skipTriv);
    void    storePb    (const vec<Lit>& ps, const vec<Int>& Cs, Int lo, Int hi);
    void    setupOccurs();   // Called on demand from 'propagate()'.
    void    findIntervals();
    bool    rewriteAlmostClauses();
    bool    convertPbs(bool first_call);   // Called from 'solve()' to convert PB constraints to clauses.

public:
    PbSolver()  : sat_solver(opt_solver == st_MiniSat)
                , ok     (sat_solver.ok_ref())
                , assigns(sat_solver.assigns_ref())
                , trail  (sat_solver.trail_ref())
                , goal(NULL)
                , formulaSize(0)
	            , numOfClouses(0)
                , propQ_head(0)
                , stats(sat_solver.stats_ref())
                , declared_n_vars(-1)
                , declared_n_constrs(-1)
	            , best_goalvalue(Int_MAX)
                {}

    // Helpers (semi-internal):
    //
    lbool   value(Var x) const { return toLbool(assigns[x]); }
    lbool   value(Lit p) const { return sign(p) ? ~toLbool(assigns[var(p)]) : toLbool(assigns[var(p)]); }
    int     nVars()      const { return assigns.size(); }
    int     nConstrs()   const { return constrs.size(); }

    // Public variables:
    BasicSolverStats& stats;

    int     declared_n_vars;            // Number of variables declared in file header (-1 = not specified).
    int     declared_n_constrs;         // Number of constraints declared in file header (-1 = not specified).
    int     pb_n_vars;                  // Actual number of variables (before clausification).
    int     pb_n_constrs;               // Actual number of constraints (before clausification).

    Map<cchar*, int>    name2index;
    vec<cchar*>         index2name;
    vec<bool>           best_model;     // Best model found (size is 'pb_n_vars').
    Int                 best_goalvalue; // Value of goal function for that model (or 'Int_MAX' if no models were found).

    // Problem specification:
    //
    int     getVar      (cchar* name);
    void    allocConstrs(int n_vars, int n_constrs);
    void    addGoal     (const vec<Lit>& ps, const vec<Int>& Cs);
    bool    addConstr   (const vec<Lit>& ps, const vec<Int>& Cs, Int rhs, int ineq, bool skipNorm);

    // Solve:
    //
    bool    okay(void) { return ok; }

    enum solve_Command { sc_Minimize, sc_FirstSolution, sc_AllSolutions };
    void solve(solve_Command cmd,bool skipSolving);    // Returns best/first solution found or Int_MAX if UNSAT.
    bool toCNF(std::vector<std::vector<Lit> >& cnf);
    bool validateResoult();  
    void cleanPBC();  
    
    			
};


//=================================================================================================

}
#endif
