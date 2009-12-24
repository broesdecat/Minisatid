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
		amnwatches.growTo(2 * nVars());
		amncountedlit.growTo(2 * nVars());
	}
}

void AMNSolver::finishECNF_DataStructures() {
	init = false;

	if (amnbound.size() > 0) {
		amnwatches.growTo(2 * nVars());
	} else {
		empty = true;
	}

	/*print useful information
	 if (verbosity >= 1){
	 //calculate number of amn statements and literals
	 //reportf("| Number of at-most-one statements: %5d",(int)amn_statements);
	 }
	 if (verbosity >= 1){
	 //calculate number of amn statements and literals
	 //reportf(", avg. size: %7.2f literals.       |\n",(double)amn_literals/(double)amn_statements);
	 }
	 if (verbosity >= 1) {
	 reportf("                                     |\n");
	 reportf("|    (there will be no at-most-one propagations)                              |\n");
	 }
	 */
}

void AMNSolver::addEE(vec<Lit>& ps, int n) {
	assert(ps.size() > 0);

	if (verbosity >= 2) {reportf("Adding EE");}

	//blijkbaar hebben beide aanpakken (met de speciale watches en zonder) alletwee voordelen
	//dus wordt momenteel de duidelijkste code gebruikt.
	vec<Lit> ps2;
	ps.copyTo(ps2);
	addAMN(ps2, n);
	ps.copyTo(ps2);
	addALN(ps2, n);
}

/**
 * Done by negating all literals and the bound and adding it as an at-most-(size-n)
 */
void AMNSolver::addALN(vec<Lit>& ps, int n) {
	assert(ps.size() > 0);

	if (verbosity >= 2) { reportf("Adding ALN"); }

	vec<Lit> ps2;
	for(int i=0; i<ps.size(); i++){
		ps2.push(~ps[i]);
	}
	int n2 = ps.size()-n;
	addAMN(ps2, n2);
	return;

	//TO REMEMBER: I tested the replicated code specifically for ALN, with separate vars and propagation
	//but the performance was exactly the same as inverting all signs and adding it as a AMN
	//even when n become large (and switching to the other form seemed usefull (but wasnt)
}

void AMNSolver::addAMN(vec<Lit>& ps, int n) {
	assert(ps.size() > 0);

	sort(ps);
	Lit previous; int i, j;
	for (i = j = 0, previous = lit_Undef; i < ps.size(); i++) {
		if (solver->value(ps[i]) == l_True) {
			n--;
		} else if (ps[i] == ~previous || ps[i] == previous)
			reportf("Encountered Exists-Unique statement containing twice the atom %d; please disambiguate.\n",var(previous)), exit(3);
		else if (solver->value(ps[i]) != l_False){
			ps[j++] = previous = ps[i];
		}
	}
	ps.shrink(i - j);

	//special case checks
	if (ps.size() <= n) { //will always be fulfilled
		return;
	}
	if( n < 0){ //will never be satisfiable
		throw theoryUNSAT;
	}

	if(n==0){ //can immediately propagate (all false), so add unit clauses
		vec<Lit> ps2(1);
		for(int i=0; i<ps.size(); i++){
			ps2[0]=~ps[i];
			solver->addClause(ps2);
		}
	}

	if (ps.size() == 2 && n == 1) { //optimization
		vec<Lit> temp(2);
		temp[0] = ~ps[0];
		temp[1] = ~ps[1];
		solver->addClause(temp);
		return;
	}

	//normal case
	Clause* c = Clause_new(ps, false);
	if (verbosity >= 2) {
		reportf("AMN clause: "); printClause(*c); reportf(" for %i\n", n);
	}

	//add clause and bound
	amnclauses.push(c);
	int index = amnclauses.size() - 1;
	amnbound.push(n);
	amncounter.push(0); //all literals that are already true have been substracted from n

	//add watches
	amnwatches.growTo(2 * nVars()); // Make sure the AMN_watches array is big enough.
	for (int i = 0; i < ps.size(); i++) {
		amnwatches[toInt(ps[i])].push(index);
	}
}

Clause* AMNSolver::amnpropagate(Lit p) {
	assert(!amncountedlit[toInt(p)]);

	vec<int>& ws = amnwatches[toInt(p)];
	if (ws.size() == 0) {
		return NULL;
	} //means that there are no amn expressions containing p

	if (verbosity >= 2) {
		reportf("AMN-propagating literal ");
		printLit(p);
		reportf(": (");
	}

	//it has to be guaranteed that ALL clauses increment their counter first,
	//otherwise a conflict might occur halfway, leaving them in an inconsistent state
	for (int i = 0; i < ws.size(); i++) {
		amncounter[ws[i]]++;
	}
	amncountedlit[toInt(p)] = true;

	for (int i = 0; i < ws.size(); i++) {
		int counter = amncounter[ws[i]], bound = amnbound[ws[i]];
		Clause& c = *amnclauses[ws[i]];

		if (counter < bound) {
			continue;
		} else {
			vec<Lit> ps;
			ps.push(); // the first one has to be the conflicted or the propagated one
			//then add all that are not the propagated one. How p is added depends on whether it is propagated or conflict
			for (int j = 0; j < c.size() && ps.size()<bound+1; j++) {
				if (value(c[j]) == l_True && p!=c[j]) {
					ps.push(~c[j]);
				}
			}

			if (counter == bound) { //add a learned clause for each unknown one, and make it FALSE
				ps.push(~p);

				vec<Lit> ps2;
				ps.copyTo(ps2);
				for (int j = 0; j < c.size(); j++) {
					if (value(c[j]) == l_Undef) {
						ps2[0]=~c[j];

						if (verbosity >= 2) { printLit(~c[j]); reportf(" "); }

						Clause* rc = Clause_new(ps2, true);
						solver->setTrue(~c[j], rc);
					}
				}
			} else { //generate a conflict clause containing all true ones
				if (verbosity >= 2){ reportf(" Conflict occurred).\n");	}

				ps[0]=~p;
				Clause* rc = Clause_new(ps, true);
				solver->addLearnedClause(rc);
				return rc;
			}
		}
	}
	if (verbosity >= 2 && ws.size() > 0) { reportf(" ).\n"); }
	return NULL;
}

void AMNSolver::cardbacktrack(Lit p) {
	if(amncountedlit[toInt(p)]){
		amncountedlit[toInt(p)] = false;
		vec<int>& ws = amnwatches[toInt(p)];
		for(int i=0; i<ws.size(); i++){
			amncounter[ws[i]]--;
		}
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


/*
CODE that is sometimes faster, because of (sometimes) good heuristic for watches with EXISTS EXACTLY

//de reden waarom de speciale EU code zoveel sneller gaat:
//er worden watches bijgehouden voor de negatieve literals, wat hetzelfde zou zijn als het toevoegen van
//een clause aan de sat solver
//MAAR als er propagatie gebeurt omdat een literal p true wordt, wordt OOK de watch in de clause gezet
//naar -p, wat een heel mooie heuristiek is duidelijk heel veel effect heeft!!!!!


@POST general case: a clause has been created with only unknown literals, sorted and without doubles
					a EU watch has been created for each of the literals in the clause

addEU(){
	sort(ps); //sorts all literals according to their numbering, such that p and ~p are neighbours!!
	vec<Lit> ps2; //temp new var
	for (int i = 0; i < ps.size(); i++) {
		if (solver->value(ps[i]) == l_True) {
			//if already true, propagate all other ones as false
			//					if another one already true, throw exception
			for (int k=i+1;k<ps.size();k++){
				if (k!=i){
					if(solver->value(ps[k])==l_True){
						throw theoryUNSAT;
					}
					solver->setTrue(~ps[k], NULL);
				}
			}
		} else if (ps[i+1] == ps[i]){//SORTED! so next to each other
			reportf("Encountered Exists-Unique statement containing twice the atom %d; please disambiguate.\n",var(ps[i])), exit(3);
		} else if (solver->value(ps[i]) == l_Undef){ //only push unknown values (optimization)
			ps2.push(ps[i]);
		}
	}

	if (ps2.size() == 0){
		throw theoryUNSAT;
	} else if (ps2.size() == 1){
		solver->setTrue(ps2[0], NULL);
	}else if (ps2.size() == 2){
		Clause* c = Clause_new(ps2, false);
		solver->addClause(c);
		ps2[0]=~ps2[0]; ps2[1]=~ps2[1];
		c = Clause_new(ps2, false);
		solver->addClause(c);
	}else{
		EU_watches.growTo(2*nVars());

		Clause* c = Clause_new(ps2, false);
		//not creating sat solver watched literals!

		//volgende regel schrappen als de code werkt
		//solver->justAddClause(c);

		EU_watches[toInt(~ps2[0])].push(c);
		EU_watches[toInt(~ps2[1])].push(c);

		for (int i=0;i<ps2.size();i++){ //create an EU watched literal for each literal (all are currently unknown)
			EU_watches[toInt(ps2[i])].push(c);
		}
	}
}

Clause* AMNSolver::EU_propagate(Lit p) {
    Clause* confl=NULL;

    //DO LATER put into finishdatastructs
    if(EU_watches.size()!=nVars()*2){
    	EU_watches.growTo(2*nVars());
    }

    vec<Clause*>& ws = EU_watches[toInt(p)];
    if(ws.size()==0){
    	return NULL;
    }
    Clause **i, **j, **end;
	for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
		Clause& c = **i++;

		// Verify whether ~p equals c[0] or c[1].
		Lit false_lit = ~p;
		if (c[0] == false_lit)
			c[0] = c[1], c[1] = false_lit;
		if (c[1] == false_lit) {
			// Search for an alternative watch if needed.
			Lit first = c[0];
			if (solver->value(first) == l_True){
				*j++ = &c;
			}else{
				for (int k = 2; k < c.size(); k++)
					if (solver->value(c[k]) != l_False){ // NOTE: if value(c[k])==l_True, then c[k] will still propagate later.
						c[1] = c[k]; c[k] = false_lit;
						EU_watches[toInt(~c[1])].push(&c);
						goto FoundEUWatch;
					}

				// Did not find watch -- clause is unit under assignment:
				*j++ = &c;
				if (solver->value(first) == l_False){
					confl = &c;
					solver->qhead = solver->trail.size();
					// Copy the remaining watches:
					while (i < end)
						*j++ = *i++;
				}else if (solver->value(first) == l_Undef)
					solver->setTrue(first, &c);
			}
		} else {
			// p is a literal of the clause: make all the rest false, and make c[0]=p.
			*j++ = &c; // Retain the watch anyhow.
			for (int k = 0; k < c.size(); k++) {
				if (c[k]==p) {
					c[k] = c[0], c[0] = p;
					if (k>1) {
						EU_watches[toInt(~c[0])].push(&c);
						vec<Clause*>& rmv_ws = EU_watches[toInt(~c[k])];
						int x=0; while (rmv_ws[x++]!=&c);
						rmv_ws[--x]=rmv_ws.last(); rmv_ws.shrink(1);
					}
				} else {
					vec<Lit> ps(2); ps[0]=~c[k]; ps[1]=~p;
					if (solver->value(ps[0])!=l_True) {
						Clause* rc = Clause_new(ps, true);
						solver->addLearnedClause(rc);
						if (solver->value(ps[0])==l_False) {
							confl = rc;
							solver->qhead = solver->trail.size();
							// Copy the remaining watches:
							while (i < end)
								*j++ = *i++;
						} else
							solver->setTrue(ps[0], rc);
					}
				}
			}
		}
FoundEUWatch:;
	}
	ws.shrink(i - j);

	return confl;
}*/
