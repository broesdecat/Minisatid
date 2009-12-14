#include "AMOSolver.h"

AMOSolver::AMOSolver():
	amo_statements(0),
	amo_literals(0),
	init(true),
	empty(false)
{
}

AMOSolver::~AMOSolver() {
}

inline lbool    AMOSolver::value(Var x) const   { return solver->value(x); 	}
inline lbool    AMOSolver::value(Lit p) const   { return solver->value(p); 	}
inline int      AMOSolver::nVars()      const   { return solver->nVars(); 	}

void AMOSolver::notifyVarAdded(){
	if (!empty) {
		AMO_watches.growTo(2 * nVars());
	}
}

bool AMOSolver::addAMO(vec<Lit>& ps) {
	assert(ps.size() > 0);
	assert(!sign(ps[0]));

	// Main calls first "addClause(vec<Lit>& ps)", where sorting etc happens. Thus, if we get here, ps has size > 0, and is sorted. If ps.size()==1, the propagation has already happened.
	if (ps.size() == 1)
		return true;
	Clause* c;
	if (ps.size() == 2) {
		ps[0] = ~ps[0];
		ps[1] = ~ps[1];
		c = Clause_new(ps, false);
		solver->addClause(c);
		ps[0] = ~ps[0];
		ps[1] = ~ps[1]; // return ps to its original state: may be used to add Clause (for EU)
	} else {
		// TODO: it should be possible, in case of an EU expression, to use the clause that's already there. Then when a literal becomes true, it can be set as watch in the clause also.
		c = Clause_new(ps, false);
		solver->addClause(c);
		if (verbosity >= 2) {
			reportf("AMO clause: ");
			printClause(*c);
			reportf("\n");
		}

		int n = 2 * nVars();
		while (n >= AMO_watches.size())
			AMO_watches.push(); // Make sure the AMO_watches array is big enough.

		for (int i = 0; i < ps.size(); i++)
			AMO_watches[toInt(ps[i])].push(c);
		amo_statements++;
		amo_literals += ps.size();
	}

	return true;
}

//=================================================================================================
// SAT(ID) additional methods

// Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
void AMOSolver::finishECNF_DataStructures() {
	init = false;
	if (verbosity >= 1)
		reportf("| Number of at-most-one statements: %5d",(int)amo_statements);
	if (amo_statements > 0) {
		if (verbosity >= 1)
			reportf(", avg. size: %7.2f literals.       |\n",(double)amo_literals/(double)amo_statements);
		int n = 2 * nVars();
		while (n >= AMO_watches.size())
			AMO_watches.push();
	} else {
		empty = true;
		if (verbosity >= 1) {
			reportf("                                     |\n");
			reportf("|    (there will be no at-most-one propagations)                              |\n");
		}
	}
}

Clause* AMOSolver::AMO_propagate(Lit p) {// TODO: if part of an EU statement, change watches there.
	vec<Clause*>& ws = AMO_watches[toInt(p)];

	if(ws.size() == 0){
		return NULL;
	}

    if (verbosity>=2 && ws.size()>0) {
    	reportf("AMO-propagating literal ");
    	printLit(p);
    	reportf(": (");
    }
    for (int i=0; i<ws.size(); i++) {
        Clause& c = *ws[i];
        vec<Lit> ps(2); ps[1]=~p;
        for (int j=0; j<c.size(); j++) {
            if (c[j]==p || value(c[j])==l_False)
                continue;
            ps[0]=~c[j];
            Clause* rc = Clause_new(ps, true);
            solver->addLearnedClause(rc);
            if (value(c[j])==l_True) {
                if (verbosity>=2) reportf(" Conflict");
                solver->qhead = solver->trail.size();
                return rc;
            } else {// (value(c[j])==l_Undef) holds
                solver->setTrue(~c[j], rc);
                if (verbosity>=2) {
                	reportf(" ");
                	printLit(c[j]);
                }
            }
        }
    }
    if (verbosity>=2 && ws.size()>0){
    	reportf(" ).\n");
    }

    return NULL;
}

//=================================================================================================
// Debug + etc:

inline void AMOSolver::printLit(Lit l){
    reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}


template<class C>
inline void AMOSolver::printClause(const C& c){
    for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}
