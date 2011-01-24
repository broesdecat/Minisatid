#include "PbSolver.h"
#include "Hardware.h"

// for _Exit(...)
#include <unistd.h>

namespace MiniSatPP {
	
//-------------------------------------------------------------------------------------------------
void    linearAddition (const Linear& c, vec<Formula>& out);        // From: PbSolver_convertAdd.C
Formula buildConstraint(const Linear& c, int max_cost = INT_MAX);   // From: PbSolver_convertSort.C
Formula convertToBdd   (const Linear& c, int max_cost = INT_MAX);   // From: PbSolver_convertBdd.C
//-------------------------------------------------------------------------------------------------

// prototype
void printBasesAndTerminate(int noc);

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

        if (opt_verbosity >= 1)
            /**/reportf("---[%4d]---> ", constrs.size() - 1 - i);

        if (opt_convert == ct_Sorters) {
            if (opt_dump) { // no formulae built
                buildConstraint(c);
            } else {
                converted_constrs.push(buildConstraint(c));
            }
        }
        else if (opt_convert == ct_Adders)
            linearAddition(c, converted_constrs);
        else if (opt_convert == ct_BDDs)
            converted_constrs.push(convertToBdd(c));
        else if (opt_convert == ct_Mixed){
            int adder_cost = estimatedAdderCost(c);
            //**/printf("estimatedAdderCost: %d\n", estimatedAdderCost(c));
            Formula result = convertToBdd(c, (int)(adder_cost * opt_bdd_thres));
            if (result == _undef_)
                result = buildConstraint(c, (int)(adder_cost * opt_sort_thres));
            if (result == _undef_)
                linearAddition(c, converted_constrs);
            else
                converted_constrs.push(result);
        }else
            assert(false);

        if (!ok) return false;
    }

    if (!opt_validateResoult) cleanPBC();
	
	formulaSize = converted_constrs.size();
	
    clausify(sat_solver, converted_constrs);
    
    if (opt_dump) {
        _Exit(0);
    }
    if (opt_only_base) {
        printBasesAndTerminate(sat_solver.numOfClouses());
    }
    if (opt_skip_sat && !opt_natlist && (opt_base_result_file != NULL)) {
        double cpuT = cpuTime();
        bool isSat = false; // whatever
        numOfClouses = sat_solver.numOfClouses();
        printBaseOutPut(cpuT,isSat,false,false);
        _Exit(0);
    }
    

    return ok;
}

// for the web interface:
// print base info and then terminate immediately
void printBasesAndTerminate(int noc) {
    while(!baseMetaData.empty()) {
        printf("Base: ");
        SearchMetaData &md = (*baseMetaData.back());
        int size = md.base.size();
        for(int i=0; i<size; i++) {
            printf("%d", md.base[i]);
            if (i != size-1) printf(",");
            else printf("; ");
        }
        printf("# Candidates: %ld; ", md.basesEvaluated);
        double searchMillis = md.runTime/1000.0;
        printf("Search Time: %.3f ms\n", searchMillis); 
        delete baseMetaData.back();
        baseMetaData.pop_back();
    }
    if (noc > 0) {
        // nasty hack to not print number of clauses for
        // optimal base problems (which are not converted to SAT)
        printf("Number of clauses: %d \n ", noc);
    }
    exit(0);
}

}
