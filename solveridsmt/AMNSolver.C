#include "AMNSolver.h"

AMNSolver::AMNSolver() :
	init(true), empty(false) {
}

AMNSolver::~AMNSolver() {
}

inline lbool AMNSolver::value(Var x) const {
	return solver->value(x);
}
inline lbool AMNSolver::value(Lit p) const {
	return solver->value(p);
}
inline int AMNSolver::nVars() const {
	return solver->nVars();
}

void AMNSolver::notifyVarAdded() {
	if (!empty) {
		AMN_watches.growTo(2 * nVars());
	}
}

void AMNSolver::addEE(vec<Lit>& ps, int n) {
	assert(ps.size() > 0 && !sign(ps[0]) && n>0);

	if (n == 1) {
		addAMN(ps, 1);
		solver->addClause(ps);
	} else {
		addAMN(ps, n);
		addALN(ps, n);
	}
}

void AMNSolver::addALN(vec<Lit>& ps, int n) {
	assert(ps.size() > 0 && n>0);

	if (ps.size() < n) { //will never be satisfiable
		throw theoryUNSAT;
	}

	//TODO rest

	throw 100;
}

void AMNSolver::addAMN(vec<Lit>& ps, int n) {
	assert(ps.size() > 0 && n>0);

	if (ps.size() <= n) { //will always be fulfilled
		return;
	}

	if (ps.size() == 2 && n == 1) { //optimization
		vec<Lit> temp(2);
		temp[0] = ~ps[0];
		temp[1] = ~ps[1];
		Clause* c = Clause_new(temp, false);
		solver->addClause(c);
		return;
	}

	//normal case
	Clause* c = Clause_new(ps, false);
	if (verbosity >= 2) {
		reportf("AMN clause: ");
		printClause(*c);
		reportf("\n");
	}

	//add clause and bound
	amn_clauses.push(c);
	int index = amn_clauses.size() - 1;
	amn_bound.push(n);

	//add watches
	AMN_watches.growTo(2 * nVars()); // Make sure the AMN_watches array is big enough.
	for (int i = 0; i < ps.size(); i++) {
		AMN_watches[toInt(ps[i])].push(index);
	}

	//FIXME steunt erop dat alle atomen eens worden gepropageerd. Is dit zeker zo?
	//amn_counter.push(0);

	//add current number of true literals
	int counter = 0;
	for (int i = 0; i < ps.size(); i++) {
		if (solver->value(ps[i]) == l_True) {
			counter++;
		}
	}
	amn_counter.push(counter);

	if (counter > n) {
		throw theoryUNSAT;
	}
}

//=================================================================================================
// SAT(ID) additional methods

void AMNSolver::finishECNF_DataStructures() {
	init = false;

	if (amn_bound.size() > 0) {
		AMN_watches.growTo(2 * nVars());
	} else {
		empty = true;
	}

	/*
	 TODO print useful information
	 if (verbosity >= 1){
	 //TODO calculate number of amn statements and literals
	 //reportf("| Number of at-most-one statements: %5d",(int)amn_statements);
	 }
	 if (verbosity >= 1){
	 //TODO calculate number of amn statements and literals
	 //reportf(", avg. size: %7.2f literals.       |\n",(double)amn_literals/(double)amn_statements);
	 }
	 if (verbosity >= 1) {
	 reportf("                                     |\n");
	 reportf("|    (there will be no at-most-one propagations)                              |\n");
	 }
	 */
}

Clause* AMNSolver::AMN_propagate(Lit p) {
	vec<int>& ws = AMN_watches[toInt(p)];
	if (ws.size() == 0) {
		return NULL;
	} //means that there are no amn expressions containing p

	if (verbosity >= 2) {
		reportf("AMN-propagating literal ");
		printLit(p);
		reportf(": (");
	}

	for (int i = 0; i < ws.size(); i++) {
		//check if propagation is possible
		amn_counter[ws[i]]++;
		int counter = amn_counter[ws[i]], bound = amn_bound[ws[i]];

		Clause& c = *amn_clauses[ws[i]];
		if (counter < bound) {
			continue;
		} else {
			//collect all that are already true (and stop early)
			vec<Lit> ps;
			for (int j = 0; j < c.size() && ps.size()<bound; j++) {
				if (value(c[j]) == l_True) {
					ps.push(~c[j]);
				}
			}

			if (counter == bound) { //add a learned clause for each unknown one, and make it FALSE
				for (int j = 0; j < c.size(); j++) {
					if (c[j] != p && value(c[j]) == l_Undef) {
						vec<Lit> ps2;
						ps.copyTo(ps2);
						ps2.push(~c[j]);

						if (verbosity >= 2) {
							reportf(" ");
							printLit(~c[j]);
						}

						Clause* rc = Clause_new(ps2, true);
						solver->setTrue(~c[j], rc);
						solver->addLearnedClause(rc);
					}
				}
			} else { //generate a conflict clause containing all true ones
				if (verbosity >= 2){
					reportf(" Conflict occurred).\n");
				}

				ps.push(~p);
				Clause* rc = Clause_new(ps, true);
				solver->addLearnedClause(rc);
				return rc;
			}
		}
	}
	if (verbosity >= 2 && ws.size() > 0) {
		reportf(" ).\n");
	}

	return NULL;
}

void AMNSolver::AMN_backtrack(Lit l) {
	vec<int>& ws = AMN_watches[toInt(l)];
	for (int i = 0; i < ws.size(); i++) {
		amn_counter[ws[i]]--;
	}
}

//=================================================================================================
// Debug + etc:

inline void AMNSolver::printLit(Lit l) {
	reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}

template<class C>
inline void AMNSolver::printClause(const C& c) {
	for (int i = 0; i < c.size(); i++) {
		printLit(c[i]);
		fprintf(stderr, " ");
	}
}
