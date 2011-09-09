#include "PB2CNF.hpp"
#include "SolverTypes.h"

using namespace std;

namespace MiniSatPP {

void toCNF(std::vector<std::vector<Lit> >& cnf, const vec<MiniSat::Clause*>& clauses, const vec<int>& assigns, const vec<int>& level){
    // Export CNF:
    for (int i = 0; i < assigns.size(); i++){
        if (assigns[i] != l_Undef && level[i] == 0) {
        	cnf.push_back(std::vector<Lit>());
        	Lit t = Lit(i,!(assigns[i] == l_True));
        	cnf.back().push_back(t);
        }
    }
    for (int i = 0; i < clauses.size(); i++){
        MiniSat::Clause& c = *clauses[i];
        cnf.push_back(std::vector<Lit>());
        for (int j = 0; j < c.size(); j++){
        	cnf.back().push_back(c[j]);
        }
    }
}

}
