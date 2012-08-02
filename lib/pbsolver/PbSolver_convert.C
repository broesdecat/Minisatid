#include "PbSolver.h"
#include "Hardware.h"

// for _exit(...)
#include <unistd.h>

namespace MiniSatPP {
	
//-------------------------------------------------------------------------------------------------
void    linearAddition (const Linear& c, vec<Formula>& out, int verbosity);        // From: PbSolver_convertAdd.C
Formula buildConstraint(const Linear& c, PrimesLoader& pl, PBOptions* options, int max_cost = INT_MAX);   // From: PbSolver_convertSort.C
Formula convertToBdd   (const Linear& c, int verbosity, int max_cost = INT_MAX);   // From: PbSolver_convertBdd.C
//-------------------------------------------------------------------------------------------------


bool PbSolver::convertPbs(bool first_call)
{
    vec<Formula>    converted_constrs;

    if (first_call){
        findIntervals();
        if (!rewriteAlmostClauses()){
            ok = false;
            return false; }
    }

    for (int i = 0; i < constrs.size(); i++){
        if (constrs[i] == NULL) continue;
        Linear& c   = *constrs[i]; assert(c.lo != Int_MIN || c.hi != Int_MAX);

        if (options->opt_verbosity >= 1)
            /**/reportf("---[%4d]---> ", constrs.size() - 1 - i);

        if (options->opt_convert == ct_Sorters) {
            if (options->opt_dump) { // no formulae built
                buildConstraint(c,primesLoader, options);
            } else {
                converted_constrs.push(buildConstraint(c,primesLoader, options));
            }
        }
        else if (options->opt_convert == ct_Adders)
            linearAddition(c, converted_constrs, options->opt_verbosity);
        else if (options->opt_convert == ct_BDDs)
            converted_constrs.push(convertToBdd(c, options->opt_verbosity));
        else if (options->opt_convert == ct_Mixed){
            int adder_cost = estimatedAdderCost(c);
            //**/printf("estimatedAdderCost: %d\n", estimatedAdderCost(c));
            Formula result = convertToBdd(c, options->opt_verbosity, (int)(adder_cost * options->opt_bdd_thres));
            if (result == _undef_)
                result = buildConstraint(c,primesLoader, options, (int)(adder_cost * options->opt_sort_thres));
            if (result == _undef_)
                linearAddition(c, converted_constrs, options->opt_verbosity);
            else
                converted_constrs.push(result);
        }else
            assert(false);

        if (!ok) return false;
    }

    if (!options->opt_validateResoult) cleanPBC();
	
	formulaSize = converted_constrs.size();
	
    clausify(*sat_solver, options, converted_constrs);
    
    if (options->opt_dump) {
        exit(0);
    }

    return ok;
}

}
