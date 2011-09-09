/**************************************************************************************************

VarOrder.h -- (C) Niklas Een, Niklas S�rensson, 2004

ADT for maintaining the variable ordering. It will keep a list of all decision
variables sorted on the current activity.

**************************************************************************************************/

#ifndef VarOrder_h
#define VarOrder_h

#include "SolverTypes.h"
#include "Heap.h"

namespace MiniSatPP {
//=================================================================================================


struct VarOrder_lt {
    const vec<double>&  activity;
    bool operator () (Var x, Var y) { return activity[x] > activity[y]; }
    VarOrder_lt(const vec<double>&  act) : activity(act) { }
};

class VarOrder {
    const vec<int>&     assigns;     // var->val. Pointer to external assignment table.
    const vec<double>&  activity;    // var->act. Pointer to external activity table.
    Heap<VarOrder_lt>   heap;
    double              random_seed; // For the internal random number generator

public:
    vec<char>           dvars;

    VarOrder(const vec<int>& ass, const vec<double>& act) :
        assigns(ass), activity(act), heap(VarOrder_lt(act)), random_seed(91648253)
        { }

    inline void newVar(bool dvar);
    inline void update(Var x);                  // Called when variable increased in activity.
    inline void undo(Var x);                    // Called when variable is unassigned and may be selected again.
    inline Var  select(double random_freq =.0); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
};


void VarOrder::newVar(bool dvar)
{
    dvars.growTo(assigns.size(),dvar);
    heap.setBounds(assigns.size());
    if (dvar)
        heap.insert(assigns.size()-1);
}


void VarOrder::update(Var x)
{
    if (heap.inHeap(x))
        heap.increase(x);
}


void VarOrder::undo(Var x)
{
    if (dvars[x] && !heap.inHeap(x))
        heap.insert(x);
}


Var VarOrder::select(double random_var_freq)
{
    // Random decision:
    if (drand(random_seed) < random_var_freq){
        Var next = irand(random_seed,assigns.size());
        if (toLbool(assigns[next]) == l_Undef)
            return next;
    }

    // Activity based decision:
    while (!heap.empty()){
        Var next = heap.getmin();
        if (toLbool(assigns[next]) == l_Undef)
            return next;
    }

    return var_Undef;
}

//=================================================================================================
}
#endif
