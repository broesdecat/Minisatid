#include "IDSolver.h"

#include "Sort.h"
#include "Map.h"
#include <cmath>

IDSolver::IDSolver():
	defn_strategy(always),
	defn_search(include_cs),
	ufs_strategy(breadth_first),
	init(true),
	prev_conflicts(-1),
//	//first time test (prev_conflicts==conflicts) should fail
//	cycle_sources(0), justifiable_cycle_sources(0),
//	cycles(0),
//	cycle_sizes(0),
//	justify_conflicts(0), // ecnf_mode.def
//	nb_times_findCS(0), justify_calls(0), cs_removed_in_justify(0),
//	succesful_justify_calls(0), extdisj_sizes(0),
//	total_marked_size(0),
//	//  , fw_propagation_attempts(0), fw_propagations(0)
	adaption_total(0),	adaption_current(0)
{
}

inline lbool    IDSolver::value(Var x) const   { return solver->value(x); }
inline lbool    IDSolver::value(Lit p) const   { return solver->value(p); }
inline int      IDSolver::nVars()      const   { return solver->nVars();  }

IDSolver::~IDSolver() {
}

//@pre: conflicts are empty
bool IDSolver::simplify(){
	// Note that ecnf_mode.init is still true, if this is the first time running simplify!
	init = false;

	// Initialization procedure to ensure correctness of subsequent indirectPropagate() calls.
	// This has to be done before the first choice.

	// NOTE: we're doing a stable model initialization here. No need for a loop.
	cf_justification_disj.clear();
	cf_justification_disj.growTo(nVars());
	sp_justification_disj.clear();
	sp_justification_disj.growTo(nVars());
	cf_justification_aggr.clear();
	cf_justification_aggr.growTo(2 * nVars());
	sp_justification_aggr.clear();
	sp_justification_aggr.growTo(2 * nVars());

	// initialize nb_body_lits_to_justify
	vec<int> nb_body_lits_to_justify;			//The number of body literals needed to be true to derive the head.
	nb_body_lits_to_justify.growTo(nVars(), 0);

	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (value(v) == l_False)
			continue;
		switch (getDefType(v)) {
		case DISJ:
			nb_body_lits_to_justify[v] = 1;
			break;
		case CONJ:
			nb_body_lits_to_justify[v] = definition[v]->size() - 1;
			break;
		case AGGR:
			nb_body_lits_to_justify[v] = 1;
			break;
		default:
			break;
		}
	}

	// initialize a queue of literals that are safe with regard to cycle-freeness. (i.e.: either are not in justification, or are justified in a cycle-free way.)
	Queue<Lit> propq;
	for (int i = 0; i < nVars(); ++i){
		if (value(i) != l_True){
			propq.insert(Lit(i, true)); // First negative literals are added that are not already false (or the positive part is not true)
		}
	}
	for (int i = 0; i < nVars(); ++i){
		if (!isDefInPosGraph(i) && value(i) != l_False){
			propq.insert(Lit(i, false)); // Then all non-false non-defined positive literals.
		}
	}

	// propagate safeness to defined literals until fixpoint.
	// While we do this, we build the initial justification.
	while (propq.size() > 0) {
		Lit l = propq.peek();
		propq.pop();

		for (int i = 0; i < disj_occurs[toInt(l)].size(); ++i) { // Find disjunctions that may be made cycle-safe through l.
			Var v = (disj_occurs[toInt(l)])[i];
			if (value(v) == l_False){
				continue;
			}
			if (nb_body_lits_to_justify[v] > 0) {
				nb_body_lits_to_justify[v] = 0;
				propq.insert(Lit(v, false));
				cf_justification_disj[v] = l;
				sp_justification_disj[v] = l;
			}
		}
		for (int i = 0; i < conj_occurs[toInt(l)].size(); ++i) { // Find conjunctions that may be made cycle-safe through l.
			Var v = (conj_occurs[toInt(l)])[i];
			if (value(v) == l_False){
				continue;
			}
			nb_body_lits_to_justify[v]--;
			if (nb_body_lits_to_justify[v] == 0){
				propq.insert(Lit(v, false));
			}
		}
		if (aggsolver!=NULL) {
			vec<vec<Lit> > jstf;
			vec<Var> v;
			aggsolver->propagateJustifications(var(l), jstf, v, nb_body_lits_to_justify);
			for(int i=0; i<v.size(); i++){
				if (nb_body_lits_to_justify[v[i]] == 0) {
					propq.insert(Lit(v[i], false));
					assert(sp_justification_aggr[v[i]].size()==0);
					assert(cf_justification_aggr[v[i]].size()==0);
					for (int j = 0; j < jstf[i].size(); ++j) {
						sp_justification_aggr[v[i]].push(jstf[i][j]);
						cf_justification_aggr[v[i]].push(jstf[i][j]);
					}
				}
			}
		}
	}

	// vars v that still have nb_body_lits_to_justify[v]>0 can never possibly become true: make them false.
	if (verbosity >= 2){
		reportf("Initialization of justification makes these atoms false: [");
	}
	vec<Lit> empty;
	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (nb_body_lits_to_justify[v] > 0) {
			if (verbosity >= 2){ reportf(" %d",v+1); }

			Lit p = Lit(v,true);
			if(value(p) != l_Undef){
				if(value(p) == l_False){
					throw theoryUNSAT;
				}
			}else{
				solver->setTrue(p, NULL);
			}

			setTypeIfNoPosLoops(v);
			--atoms_in_pos_loops;
		}
	}
	if (verbosity >= 2){
		reportf(" ]\n");
	}

	if (atoms_in_pos_loops == 0){
		solver->setIDSolver(NULL); //TODO hier een methode voor maken
		aggsolver->setIDSolver(NULL);
		if (atoms_in_pos_loops == 0 && verbosity >= 1){
			reportf("| All recursive atoms falsified in initializations.                           |\n");
		}
	}

	return true;
}

DefType IDSolver::getDefType(Var v){
	if(definition[v]==NULL){
		return NONDEFALL;
	}else{
		return definition[v]->getType();
	}
}

bool IDSolver::isDefInPosGraph(Var v){
	if(getDefType(v)==NONDEFALL || getDefType(v)==NONDEFPOS){
		return false;
	}
	return true;
}

void IDSolver::notifyVarAdded(){
	seen.push(0);
	seen2.push(0);

	definition.push(NULL);
	disj_occurs.growTo(2 * nVars()); // May be tested on in findCycleSources().
	conj_occurs.growTo(2 * nVars()); // Probably not needed anyway...
}

/**
 * First literal in ps is the head of the rule. It has to be present and it has to be positive.
 *
 * if no body literals: empty set conjunction is TRUE, empty set disjunction is FALSE!
 *
 * If CONJ, then all body literals are inverted to create the completion clause
 * else, the head atom is inverted for the completion
 *
 * If only one body literal, the clause is always made conjunctive (for algorithmic correctness later on), semantics are the same.
 */
void IDSolver::addRule(bool conj, vec<Lit>& ps) {
	assert(ps.size() > 0);
	assert(!sign(ps[0]));

	if (ps.size() == 1) {
		Lit head = conj?ps[0]:~ps[0]; //empty set conj = true, empty set disj = false
		if (value(head) == l_False){
			throw theoryUNSAT;
		}
		vec<Lit> v;
		v.push(head);
		solver->addClause(v);
	} else {
		//rules with only one body atom have to be treated as conjunctive
		conj = conj || ps.size()==2;

		Rule* r = new Rule(ps, conj);
		defdVars.push(var(ps[0]));
		definition[var(ps[0])] = r;

		//create completions
		if (conj){
			for (int i = 1; i < ps.size(); i++){
				ps[i] = ~ps[i];
			}
		}else{
			ps[0] = ~ps[0];
		}

		vec<Lit> temp; //because addclause empties temp
		ps.copyTo(temp);
		solver->addClause(temp);

		for (int i = 1; i < ps.size(); i++) {
			vec<Lit> binclause(2);
			binclause[0] = ~ps[0];
			binclause[1] = ~ps[i];
			solver->addClause(binclause);
		}
	}
}

//=================================================================================================
// SAT(ID) additional methods

// Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
bool IDSolver::finishECNF_DataStructures() {
	init = false;

	if (verbosity >= 1){
		reportf("| Number of rules           : %6d                                          |\n",defdVars.size());
	}

	// ****** Based on this, initialize "scc". ******
	scc.growTo(nVars(), 0);
	//for memory efficiency, the scc datastructure is used to keep the root of the nodes
	//in the end, the algorithm sets ALL of the nodes on the stack to the same root
	//so then the SCC is correct
	vec<int> & root = scc;
	vec<bool> incomp(nVars(), false);
	vec<int> stack;
	vec<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to a unique value (the counter).
	int counter = 1;

	for (int i=0; i<nVars(); i++){
		if (isDefInPosGraph(i) && visited[i]==0){
			visit(i,root,incomp,stack,visited,counter);
		}
	}

	// Based on "scc", determine which atoms should actually be considered defined. Meanwhile initialize "disj_occurs" and "conj_occurs".
	// NOTE: because we've searched scc's in the *positive* dependency graph, rules like  P <- ~Q, Q <- ~P will be marked NONDEF here. Hence final well-foundedness check needs to check in defdVars.
	atoms_in_pos_loops = 0;
	disj_occurs.growTo(2 * nVars());
	conj_occurs.growTo(2 * nVars());
	Lit l;
	Lit jstf;
	for (int i = 0; i < defdVars.size(); ++i) {
		Var v = defdVars[i];
		bool isdefd = false;
		switch (getDefType(v)) {
		case DISJ: {
			Rule& dfn = *definition[v];
			for (int j = 0; j < dfn.size(); ++j) {
				l = dfn[j];
				if (l != Lit(v, true))
					disj_occurs[toInt(l)].push(v);
				if (!sign(l) && scc[v] == scc[var(l)])
					isdefd = true;
			}
			break;
		}
		case CONJ: {
			Rule& dfn = *definition[v];
			for (int j = 0; j < dfn.size(); ++j) {
				l = ~dfn[j];
				if (l != Lit(v, true))
					conj_occurs[toInt(l)].push(v);
				if (!sign(l) && scc[v] == scc[var(l)])
					isdefd = true;
			}
			break;
		}
		case AGGR: {
			if(aggsolver!=NULL){
				vec<Lit> lits;
				aggsolver->getLiteralsOfAggr(v, lits);
				/*
				 * TODO eigenlijk is het niet logisch om aggregaten te behandelen als rules als dit niet zo geschreven is
				 * het party-goer probleem is een voorbeeld
				 * momenteel zorgt de grounder ervoor dat het via een equivalentie uitgeschreven als geen rule bedoeld is
				 * zodat de semantiek toch completion semantiek wordt, maar eigenlijk zou het groundformaat moeten aangeven of het een rule is of niet
				 */
				for (int j = 0; !isdefd && j < lits.size(); ++j){
					if (scc[v] == scc[var(lits[j])]){ // NOTE: disregard sign here: set literals can occur both pos and neg in justifications. This could possibly be made more precise for MIN and MAX...
						isdefd = true;
					}
				}
			}
			break;
		}
		default:
			assert(false);
		}
		if (isdefd){
			atoms_in_pos_loops++;
		}else{
			setTypeIfNoPosLoops(v);
		}
	}
	if (verbosity >= 1){
		reportf("| Number of recursive atoms : %6d                                          |\n",(int)atoms_in_pos_loops);
	}


	if (atoms_in_pos_loops == 0) {
		return false;
	}

	isCS.growTo(nVars(), false);

	return true;
}

void IDSolver::setTypeIfNoPosLoops(Var v){
	bool found = false;
	Rule& r = *definition[v];
	for(int i=0; i<r.size(); i++){
		if(definition[var(r[i])]!=NULL && sign(definition[v]->operator [](i))){
			found = true;
		}
	}
	if(found){
		definition[v]->setType(NONDEFPOS);
	}else{
		delete definition[v];
		definition[v] = NULL;
	}
	//FIXME also delete defdvars then?
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the
 * POSITIVE dependency graph.
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter) {
	assert(isDefInPosGraph(i));
	assert(!incomp[i]);
	visited[i] = ++counter;
	root[i] = i;
	stack.push(i);

	//FIXME FIXME TODO TODO: rewrite all signs, values, ... in function of Rule, in which NO INVERSION has taken place

	switch (getDefType(i)) {
	case DISJ: {
		for (int j = 0; j < definition[i]->size(); ++j) {
			Lit l = (*definition[i])[j];
			int w = var(l);
			if (isDefInPosGraph(w) && i != w && !sign(l)) {
				if (visited[w]==0){
					visit(w,root,incomp,stack,visited,counter);
				}
				if (!incomp[w] && visited[root[i]]>visited[root[w]]){
					root[i] = root[w];
				}
			}
		}
		break;
	}
	case CONJ: {
		for (int j = 0; j < definition[i]->size(); ++j) {
			Lit l = (*definition[i])[j];
			int w = var(l);
			//een conjunctieve rule wordt ALTIJD uitgeschreven (completion) als head OR not bodyx OR not bodyx2 ...
			//dus een conjunctieve rule gaat altijd al zijn positieve defined kinderen volgen
			if (isDefInPosGraph(w) && i != w && sign(l)) {
				if (visited[w]==0){
					visit(w,root,incomp,stack,visited,counter);
				}
				if (!incomp[w] && visited[root[i]]>visited[root[w]]){
					root[i] = root[w];
				}
			}
		}
		break;
	}
	case AGGR: {
		vec<Lit> lits;
		aggsolver->getLiteralsOfAggr(i, lits);
		for (int j = 0; j < lits.size(); ++j) {
			Var w = var(lits[j]);
			if (isDefInPosGraph(w)) {
				if (visited[w]==0){
					visit(w,root,incomp,stack,visited,counter);
				}
				if (!incomp[w] && visited[root[i]]>visited[root[w]]){
					root[i] = root[w];
				}
			}
		}
		break;
	}
	default:
		assert(false);
	}
	if (root[i] == i) {
		int w;
		do {
			w = stack.last();
			stack.pop();
			//these are the found sccs
			root[w] = i;
			incomp[w] = true;
		} while (w != i);
	}
}

/**
 * Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void IDSolver::findCycleSources() {
	clearCycleSources();
	clear_changes();

	//TODO mag prevconflicts hier niet weg (of alleszins de -1 beginwaarde?)
	if (prev_conflicts == solver->conflicts && defn_strategy == always && solver->decisionLevel()!=0) {
		for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
			Lit l = solver->getRecentAssignments(i);

			//make each head a cycle source if the cf just of the head pointed to literal ~l (which has become false)
			//and the head is currently not false
			vec<Var>& ds = disj_occurs[toInt(~l)];
			for (int j = 0; j < ds.size(); j++) {
				Var v = ds[j];
				if (value(v) != l_False && cf_justification_disj[v] == ~l) { // No support anymore; just has to change.
					findCycleSources(v);
				}
			}

			if(aggsolver!=NULL){
				aggsolver->findCycleSourcesFromBody(l);
			}
		}
	} else {
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		prev_conflicts = solver->conflicts;
		for (int i = 0; i < defdVars.size(); i++) {
			Var v = defdVars[i];

			//each head that has a false body literal which is its justification is a cycle source
			if (getDefType(v) == DISJ) {
				if (value(v) != l_False && value(cf_justification_disj[v]) == l_False){
					findCycleSources(v);
				}
			}else if (getDefType(v) == AGGR) {
				aggsolver->findCycleSourcesFromHead(v);
			}
		}
	}
	//nb_times_findCS++;
	//cycle_sources += css.size();
	if (verbosity >= 2) {
		reportf("Indirect propagations. Verifying %d cycle sources:",css.size());
		for (int i = 0; i < css.size(); ++i)
			reportf(" %d",css[i]+1);
		reportf(".\n");
	}
}

/*
 * Precondition: V is of type DISJ. It is non-false, and its cf_justification does not support it.
 * Postcondition: sp_justification..[v] supports v. v is added a cycle source if necessary (i.e., if there might be a cycle through its sp_justification).
 *
 * Only called by findCycleSources()
 */
void IDSolver::findCycleSources(Var v) {
	if(isCS[v]){
		return;
	}
	Rule& c = *definition[v];
	//NOTE: this is the only place where the invariant was used that minisat orders the literals in a clause in such a way that
	//		the first and second literal are the watches of the 2-watched DPLL
	int i=0;
	while(value(c[i])==l_False){ i++; }	//find the index of the first literal that is not false
	cycleSourceDisj(v, c[i], !sign(c[i])); // We will use c[i] this literal as the supporting literal.
}

void IDSolver::cycleSourceDisj(Var v, Lit jstf, bool becamecyclesource){
	change_jstfc_disj(v,jstf);
	if (!sign(jstf) && isDefInPosGraph(var(jstf)) && scc[v]==scc[var(jstf)]){
		addCycleSource(v);
	}
}

/*
 * Return true if indirectpropagation is necessary
 */
bool IDSolver::indirectPropagateNow() {
	if (defn_strategy == always)
		return true;
	// Decide if state is two-valued (then we definitely have to search).
	if (!solver->existsUnknownVar()) {
		if (defn_strategy == lazy)
			return false;
		if (defn_strategy == adaptive && adaption_current < adaption_total) {
			adaption_current++;
			return false;
		}
	}
	return true;
}

//TODO voorlopig wordt er nog overal met completion clauses gewerkt, die dus altijd een disjunctie zijn en geordend zoals minisat er zin in heeft, dus checken voor head en dergelijke


/*_________________________________________________________________________________________________
 |
 |  indirectPropagate : [void]  ->  [Clause*]
 |
 |  Description:
 |    If there is an unfounded set w.r.t. current assignment, this method will find one. There
 |    are then two possible results:
 |    - Making all unfounded set atoms false would result in a conflict. There will be no new
 |      elements on the propagation queue, and the conflicting loop formula is added to the theory
 |      and returned.
 |    - For each atom of the unfounded set a loop formula is added to the theory, and used as
 |      reason clause for making the atom false. Thus the propagation queue is not empty. NULL is
 |      returned.
 |    Otherwise, the justification and the watches will be adjusted and 'aligned', such that the
 |    justification is loop-free.
 |________________________________________________________________________________________________@*/
Clause* IDSolver::indirectPropagate() {
	if (!indirectPropagateNow()) {
		return NULL;
	}

	findCycleSources();

	bool ufs_found = false;
	std::set<Var> ufs;

	//uint64_t old_justify_calls = justify_calls;
 	int j=0;

 	if(ufs_strategy==depth_first){
 		int visittime = 1;	//time at which NO node has been visited yet
 		vec<Var> stack;
 		/* the seen2 variable is used to indicate:
 		 * 		that a value has been visited (and its number is the time at which it was visited
 		 * 		0 means not yet visited
 		 * 		a negative value means that it has been visited at the abs value and that it has
 		 * 		already received a valid justification
 		 */
 		//int offset;
 		vec<Var> tempseen; //used to keep the visited nodes, that have to be reset in seen2

 		for (; !ufs_found && j < css.size(); j++){//hij komt nooit in het geval dat hij iets op de stack moet pushen, altijd disj unfounded???
 			if(isCS[css[j]] && seen[css[j]]==0){
 				//TODO om geen seen2 nodig te hebben, mag dat niet tegelijk gebruikt kunnen worden in unfounded()
 				vec<vec<Lit> > network;	//maps a node to a list of nodes that have visited the first one
										//as index, the visited time is used

 				//offset gaat nog mis omdat niet alles een justification moet hebben, maar dat ze wel aan het netwerk worden toegevoegd als dat niet zo is
 				//offset = visittime-1;
 				network.growTo(visittime+1);
 				network[visittime].push(Lit(css[j]));
 				UFS ret = visitForUFSsimple(css[j], ufs, visittime, stack, seen2, network, tempseen);
 				switch(ret){
 				case UFSFOUND:
 					ufs_found = true;
 					break;
 				case NOTUNFOUNDED:
 					break;
 				case STILLPOSSIBLE:
 					break;
 				case OLDCHECK:
 					ufs_found = unfounded(css[j], ufs);
 					break;
 				}
 			}
 		}
 		for (int i = 0; i < nVars()/*tempseen.size()*/; i++) {
			//seen2[tempseen[i]] = 0;
 			seen2[i] = 0;
		}
 	}else{
 		for (; !ufs_found && j < css.size(); j++){
			if(isCS[css[j]]){
				//printClause(*definition[css[j]]);
				ufs_found = unfounded(css[j], ufs);
			}
		}
 	}

 	if(verbosity>0){
 		if(ufs_found){
 			fprintf(stderr, "UFSfound, size %i\n", ufs.size());
 		}else{
 		//	fprintf(stderr, "no ufs found\n");
 		}
	}

	//justifiable_cycle_sources += ufs_found ? (j - 1) : j; // This includes those that are removed inside "unfounded".
	//succesful_justify_calls += (justify_calls - old_justify_calls); //no longer correct for tarjan algo

	if (ufs_found) {
		if (verbosity >= 2) {
			reportf("Found an unfounded set of size %d: {",ufs.size());
			for (std::set<Var>::iterator it = ufs.begin(); it != ufs.end(); ++it)
				reportf(" %d",*it+1);
			reportf(" }.\n");
		}
		//cycles++;
		//cycle_sizes += ufs.size();
		if (defn_strategy == adaptive)
			adaption_current++; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
		return assertUnfoundedSet(ufs);
	} else { // Found a witness justification.
		apply_changes();
		if (defn_strategy == adaptive) {
			if (adaption_current == adaption_total)
				adaption_total++; // Next time, skip one decision level extra.
			else
				adaption_total--;
			if (adaption_total < 0)
				adaption_total = 0;
			adaption_current = 0;
		}
		// fwIndirectPropagate();
		// NB: nb of witnesses found == nb of decisions made in case of "always"
		//if (verbosity>=2) assert(isCycleFree()); // Only debugging! Time consuming.
		return NULL;
	}
}

bool IDSolver::unfounded(Var cs, std::set<Var>& ufs) {
	//justify_calls++;
	bool rslt = false; // if we go straight to Finish, this will be the result.
	vec<Var> tmpseen; // use to speed up the cleaning of data structures in "Finish"
	Queue<Var> q;
	Var v;
	markNonJustified(cs, tmpseen);
	if (!seen[cs]) {
		isCS[cs] = false;
		goto Finish;
	} // 'seen[v]' means: v has path to cs in current sp_justification.

	q.insert(cs);
	ufs.clear();
	ufs.insert(cs);

	while (q.size() > 0) {
		v = q.peek();
		q.pop();
		if (!seen[v]){
			continue;
		}
		if (directlyJustifiable(v, ufs, q)){
			if (Justify(v, cs, ufs, q)){
				goto Finish;
			}
		}
	}
	assert(ufs.size() > 0); // The ufs atoms form an unfounded set. 'cs' is in it.
	rslt = true;
	Finish: for (int i = 0; i < tmpseen.size(); i++) {
		seen[tmpseen[i]] = 0; /*used_conj[tmpseen[i]].clear(); WITH guards system*/
	}
	return rslt;
}

inline bool IDSolver::isJustified(Var x){
	return seen[x]==0;
}

//TODO dit steunt erop dat er als clause wordt opgeslagen
/**
 * Returns true if literal x as a body literal is positive (and because of the storing with inverted signs as clause, it
 * is positive if it has a sign)
 */
inline bool IDSolver::isPositiveBodyL(Lit x){
	return sign(x);
}

// Helper for 'unfounded(..)'. True if v can be immediately justified by one change_justification action.
/**
 * Checks the rule in which v is the head to check whether it is justified by its body at the moment.
 * If this is the case, true is returned.
 * Else, add all nonjustified body literals to the queue that have to be propagated (no negative body literals in a rule)
 *
 * seen is used as a justification mark/counter: seen==0 means is-justified
 *
 * Conjunction:
 * 		justified if seen or if negative literal
 * 		all nonjustified body literals
 */
bool IDSolver::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q) {
	bool vcanbejustified = false;
	switch (getDefType(v)) {
	case CONJ: {
		Rule& c = *definition[v];
		// NOTE: clause representation, so sign(c[i]) will fail for the head literal; body literals have an INVERTED sign
		int nonjustified = 0;
		for (int i=0; i < c.size(); ++i){
			Var x = var(c[i]);
			if (!isJustified(x) && isPositiveBodyL(c[i])) {	//positive, nonjustified literal
				nonjustified++;
				std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(x);
				if (pr.second){ //is in fact a duplicate check, previous insert returns true if it was inserted into the ufs SET
					q.insert(x);
				}
			}
		}
		if (nonjustified==0){
			vcanbejustified = true; // Each body literal has either !sign (is NEGATIVE) or !seen (is justified wrt v).
		}else{
			seen[v]=nonjustified;
		}

		/* // WITH guards system
		// Find a non-justified body literal, preferably in ufs.
		// - If not found: bottom up propagation
		// - If found: set conjunction's watch to it; make sure it's ufs and on queue.
		 Var candidate = var(c[i]);    // Else: this var is non-justified, but might not be ufs.
		 for (; i<c.size() && !(sign(c[i]) && seen[var(c[i])] && ufs.find(var(c[i])) != ufs.end()); ++i);
		 if (i==c.size()) {
		 ufs.insert(candidate);
		 q.insert(candidate);
		 used_conj[candidate].push(v);
		 } else
		 used_conj[var(c[i])].push(v); // non-justified AND already ufs.
		 */
		// WITHOUT guards system. Use 'seen[v]' as a counter: number of 'seen' body literals!
		break;
	}
	case DISJ: {
		Rule& c = *definition[v];
		// Find a justified non-false body literal.
		// - If found: set watch to it; bottom up propagation
		// - If not found: touch all non-false body literals; add them to queue.
		for (int i = 0; i < c.size(); ++i) {
			Lit bdl = c[i];
			Var b = var(bdl);
			if (value(bdl) != l_False && bdl != Lit(v, true)) { //only look at positive literals that are not false
				//TODO in prev if, a body literal==~head is not used, but why?
				//bdl is not false, so if it is positive, then it is a justification, otherwise if it is already justified, then also
				if (isPositiveBodyL(bdl) || isJustified(b)) {
					change_jstfc_disj(v, bdl);
					vcanbejustified = true;
					break;
				} else{
					std::pair<std::set<Var>::iterator, bool> pr = ufs.insert(b);
					if (pr.second){
						q.insert(b);
					}
				}
			}
		}
		break;
	}
	case AGGR: {
		vec<Lit> justification;
		aggsolver->directlyJustifiable(v, ufs, q, justification, seen, scc);
		if(justification.size()!=0){
			change_jstfc_aggr(v, justification);
			vcanbejustified = true;
		}
		//TODO: idsolver should not directly call aggregate expressions in other places, but go through the aggregate SOLVER
		break;
	}
	default:
		assert(false);
	}

	return vcanbejustified;
}

// Helper for 'unfounded(..)'. Propagate the fact that 'v' is now justified. True if 'cs' is now justified.
bool IDSolver::Justify(Var v, Var cs, std::set<Var>& ufs, Queue<Var>& q) {
	Queue<Var> tojustify;
	tojustify.insert(v); // ... starting with v.
	while (tojustify.size() > 0) {
		Var k = tojustify.peek();
		tojustify.pop();
		if (!isJustified(k)) { // Prevent infinite loop.
			// Make it justified.
			ufs.erase(k);
			seen[k]=0;
			if (isCS[k]) {
				isCS[k] = false;
				//cs_removed_in_justify++;
			}
			if (k == cs)
				return true;

			// Record also disjunctions that now become justified for bottom-up propagation.
			vec<Var>& disjs = disj_occurs[k + k]; // k+k is the index of the positive literal k.
			for (int i = 0; i < disjs.size(); ++i) {
				Var d = disjs[i];
				if (seen[d]) { // && ufs.find(d) != ufs.end()) //   WITH this extra test: only bottom-up propagate in already marked literals.
					change_jstfc_disj(d, Lit(k, false));
					tojustify.insert(d);
				}
			}

			// Record conjunctions that might now be justified on the main queue.
			/*            // WITH guards system
			 vec<Var>& conjs = used_conj[k];
			 for (int i=0; i<conjs.size(); ++i)
			 if (ufs.find(conjs[i]) != ufs.end())
			 q.insert(conjs[i]);
			 */
			// WITHOUT guards system.
			vec<Var>& conjs = conj_occurs[k + k];
			for (int i = 0; i < conjs.size(); ++i) {
				Var c = conjs[i];
				if (seen[c] && ufs.find(conjs[i]) != ufs.end()) { //  NOTE: we use 'seen' as a counter, but the counter is set *only* for literals in ufs. So the extra test is required here.
					if (seen[c] == 1)
						tojustify.insert(c); // Recall that the if-test in the beginning checks whether the atom is 'seen'.
					else
						seen[c]--;
				}
			}

			if(aggsolver!=NULL){
				// Record aggregates that might now be justified on the main queue. TODO : can we do this less eagerly? something like used_conjs?
				vec<Var> heads;
				aggsolver->getHeadsOfAggrInWhichOccurs(k, heads);
				for (int i = 0; i < heads.size(); ++i) {
					Var d = heads[i];
					if (seen[d]){ //  && ufs.find(d) != ufs.end())  WITH this extra test: only bottom-up propagate in already marked literals.
						q.insert(d);
					}
				}
			}
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void IDSolver::change_jstfc_disj(Var v, Lit j) {
	assert(getDefType(v)==DISJ);
	sp_justification_disj[v] = j;
	changed_vars.push(v);
}

// Change sp_justification: v is now justified by j.
void IDSolver::change_jstfc_aggr(Var v, const vec<Lit>& j) {
	// NOTE: maybe more efficient implementation possible if j changes very little from previous justification? Especially for MIN and MAX.
	assert(getDefType(v)==AGGR);
	sp_justification_aggr[v].clear();
	for (int i = 0; i < j.size(); i++){
		sp_justification_aggr[v].push(j[i]);
	}
	changed_vars.push(v);
}

/////
//Justification algorithm using TARJAN
/*
 * Given a tarjan execution and at some a justification is found. How to propagate it through the nodes
 * that have already been visited?
 * Keep track of which nodes have been visited by who. When a supporting justification is found, that has
 * to be followed in the opposite way:
 * if x is the justifying literal, then change the justification of all the nodes who visited (OR CHECKED to visit) x. Queue all
 * those nodes.
 * Then go through the queue, and recursively change the justification of all the nodes who visited the one
 * in the queue to the node chosen from the queue. And add the changed ones to the queue. Keep doing this
 * until the queue is empty. If a justification has already been changed, don't change it again.
 * Check that by keeping an extra justification datastructure, which is copied into sp_just when finished
 *
 * what to do for conjunctions? just skip them
 *
 */
void IDSolver::changeJustifications(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& vis){
	vec<Lit> queue;

	if(!hasJustification(definednode, vis)){
		change_jstfc_disj(definednode, firstjustification);
		vis[definednode]=-vis[definednode]; //set it as justified
		queue.push(Lit(definednode));
	}

	while(queue.size()>0){
		Lit just = queue.last();
		queue.pop();
		for(int i=0; i<network[visitedAt(var(just), vis)].size(); i++){
			Lit t = network[visitedAt(var(just), vis)][i];
			if(!hasJustification(var(t), vis)){
				change_jstfc_disj(var(t), just);
				vis[var(t)]=-vis[var(t)];
				queue.push(t);
			}
		}
	}
}

inline bool IDSolver::visitedEarlier(Var x, Var y, vec<Var>& vis){
	int x1 = vis[x]>0?vis[x]:-vis[x];
	int y1 = vis[y]>0?vis[y]:-vis[y];
	return x1<y1;
}

inline bool IDSolver::visited(Var x, vec<Var>& vis){
	return vis[x]!=0;
}

inline int IDSolver::visitedAt(Var x, vec<Var>& vis){
	return vis[x]>0?vis[x]:-vis[x];
}

inline bool IDSolver::hasJustification(Var x, vec<Var>& vis){
	return vis[x]<0;
}

/////////////
//Finding unfounded checks by
//validjust indicates both that the element is already in a justification or is in another found component (in which case it might also be false, not requiring a justification)
//TODO werkt niet voor aggregaten
UFS IDSolver::visitForUFSsimple(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& vis, vec<vec<Lit> >& network, vec<Var>& tempseen){
	vis[v]=visittime;
	int timevisited = visittime;
	visittime++;
	tempseen.push(v);

	DefType type = getDefType(v);

	if(type==AGGR){return OLDCHECK;}
	assert(type==CONJ || type==DISJ);

	Rule* c = definition[v];
	if(solver->verbosity >=1){
		printClause(*c);
	}

	Lit definedChild;
	bool childfound = false;

	for(int i=0; i<c->size(); i++){
		DefType childtype = getDefType(var(c->operator [](i)));
		Lit l = c->operator [](i);
		if(var(l)==v){ continue; } //rule head or identical body atom
		if(childtype==AGGR){return OLDCHECK;}
		if(!isDefInPosGraph(var(c->operator [](i))) || scc[var(l)]!=scc[v] || hasJustification(var(l), vis)){
			if(value(l)!=l_False && type==DISJ){
				changeJustifications(v, l, network, vis);
				return NOTUNFOUNDED;
			}
		}
		if(type==CONJ){
			if(childfound){
				 definedChild = l;
				 childfound = true;
			}else{
				return OLDCHECK;
			}
		}
	}

	stack.push(v);

	if(type==CONJ){
		if(childfound){
			if(visited(var(definedChild), vis)){
				network.growTo(visittime+1);
				network[visittime].push(Lit(v));
			}else{
				network[visitedAt(var(definedChild), vis)].push(Lit(v));
			}

			if(!visited(var(definedChild), vis)){
				UFS ret = visitForUFSsimple(var(definedChild), ufs, visittime, stack, vis, network, tempseen);
				if(ret != STILLPOSSIBLE){
					return ret;
				}
			}
			if(!hasJustification(var(definedChild), vis) && visitedEarlier(var(definedChild), v, vis)){
				vis[v]=vis[var(definedChild)];
			}
		}
	}else{ //DISJ, have returned from all others
		for(int i=0; i<c->size(); i++){
			Var child = var(c->operator [](i));
			if(child==v){ continue;	}
			if(!(getDefType(child)==CONJ || getDefType(child)==DISJ)){continue;}

			if(!visited(child, vis)){
				network.growTo(visittime+1);
				network[visittime].push(Lit(v));
			}else{
				network[visitedAt(child, vis)].push(Lit(v));
			}

			if(!visited(child, vis)){
				UFS ret = visitForUFSsimple(child, ufs, visittime, stack, vis, network, tempseen);
				if(ret!=STILLPOSSIBLE){
					return ret;
				}
			}
			if(!hasJustification(child, vis) && visitedEarlier(child, v, vis)){
				vis[v]=vis[child];
			}
		}
	}

	if(visitedAt(v, vis)==timevisited){
		bool allfalse = true;
		Var x;
		do{
			x=stack.last();
			stack.pop();
			vis[x]=vis[x]>0?vis[x]:-vis[x];
			ufs.insert(x);
			if(value(x)!=l_False){allfalse = false;}
		}while(x!=v);
		if(allfalse){
			ufs.clear();
			return STILLPOSSIBLE;
		}
		if(ufs.size()>1){
			if(solver->verbosity >=4){
				fprintf(stderr, "ufsfound: ");
				for(std::set<Var>::iterator i=ufs.begin(); i!=ufs.end(); i++){
					Var x = *i;
					fprintf(stderr, "%d:%c", x << 1, value(x) == l_True ? '1' : (value(x) == l_False ? '0' : 'X'));
				}
				fprintf(stderr, "\n");
			}
			return UFSFOUND;
		}else{
			int containsx = 0;
			for(int i=0; i<c->size(); i++){
				if(x==var(c->operator [](i))){
					containsx++;
				}
			}
			if(containsx>1){ //there is a loop of length 1, so x itself is an UFS
				if(solver->verbosity >=4){
					fprintf(stderr, "ufsfound: ");
					for(std::set<Var>::iterator i=ufs.begin(); i!=ufs.end(); i++){
						Var x = *i;
						fprintf(stderr, "%d:%c", x << 1, value(x) == l_True ? '1' : (value(x) == l_False ? '0' : 'X'));
					}
					fprintf(stderr, "\n");
				}
				return UFSFOUND;
			}else{//no loops, x is only an SCC, not a UFS
				ufs.clear();
			}
		}
	}

	return STILLPOSSIBLE;
}

//END TARJAN ALGORITHM

/**
 * Creates the loop formula given an unfounded set
 *
 * form: UFSLITERAL IMPLIES DISJUNCTION(external disjuncts)
 */
void IDSolver::createLoopFormula(const std::set<Var>& ufs, vec<Lit>& loopf){
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		switch (getDefType(*tch)) {
		case CONJ:
			break;
		case DISJ:
			{
				Rule& cl = *definition[*tch];
				for (int i = 0; i < cl.size(); i++) {
					Lit l = cl[i];
					if (l != Lit(*tch, true) && seen[var(l)] != (sign(l) ? 1 : 2) && ufs.find(var(cl[i])) == ufs.end()) {
						loopf.push(l);
						seen[var(l)] = (sign(l) ? 1 : 2); // Just in case P and ~P both appear; otherwise we might get something between well-founded and ultimate semantics...
					}
				}
				break;
			}
		case AGGR:
			aggsolver->createLoopFormula(*tch, ufs, loopf, seen);
			break;
		default:
			assert(false);
			break;
		}
	}
}

/**
 * If an atom of 'ufs' was already true, return a loop formula for this (one
 * such) atom as conflicting clause.
 * Otherwise, add a loop formula for each atom in ufs, enqueue the negation of
 * each of those atoms, and return NULL.
 * For each atom in UFS that is false, don't do anything
 *
 * Loop formulas are created in the form
 * UFSLITERAL IMPLIES DISJUNCTION(external disjuncts)
 */
Clause* IDSolver::assertUnfoundedSet(const std::set<Var>& ufs) {
	assert(!ufs.empty());

	// Create the loop formula: add the antecedents (first element will be filled in later).
	vec<Lit> loopf(1);
	createLoopFormula(ufs, loopf);

	for (int i = 1; i < loopf.size(); i++){
		seen[var(loopf[i])]=0;
	}
	//extdisj_sizes += loopf.size() - 1;

	if (defn_strategy != always) {// Maybe the loop formula could have been derived at an earlier level: in that case we first have to backtrack to that level.
		// Set the backtrack level.
		int lvl = 0;
		for (int i = 1; i < loopf.size(); i++)
			if (solver->getLevel(var(loopf[i])) > lvl)
				lvl = solver->getLevel(var(loopf[i]));
		solver->backtrackTo(lvl);
	}

	// Verify whether a conflict ensues.
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		Var v = *tch;
		if (value(v) == l_True) {
			loopf[0] = Lit(v, true);
			Clause* c = Clause_new(loopf, true);
			solver->addLearnedClause(c);
			if (verbosity >= 2) {
				reportf("Adding conflicting loop formula: [ ");
				printClause(*c);
				reportf("].\n");
			}
			//justify_conflicts++;
			return c;
		}
	}

	// No conflict: then enqueue all facts and their loop formulas.
	if (loopf.size() >= 5) { // Then we introduce a new variable for the antecedent part.
        Var v = solver->newVar();
        if (verbosity>=2) {reportf("Adding new variable for loop formulas: %d.\n",v+1);}
        // v \equiv \bigvee\extdisj{L}
        // ~v \vee \bigvee\extdisj{L}.
        loopf[0] = Lit(v,true); Clause* c = Clause_new(loopf, true);
        solver->addLearnedClause(c);
        if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        solver->setTrue(loopf[0], c);
        // \bigwedge_{d\in\extdisj{L}} v \vee ~d.
        vec<Lit> binaryclause(2); binaryclause[0] = Lit(v,false);
        for (int i=1; i<loopf.size(); ++i) {
            binaryclause[1] = ~loopf[i];
            Clause* c = Clause_new(binaryclause, true);
            solver->addLearnedClause(c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }

        // \bigwedge_{l\in L} \neg l \vee v
        binaryclause[1] = Lit(v,false);
        for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
            binaryclause[0] = Lit(*tch,true); Clause* c = Clause_new(binaryclause, true);
            solver->addLearnedClause(c);
            //solver->uncheckedEnqueue(binaryclause[0], c);
            if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        }
    } else { // We simply add the loop formula as is.
        for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
        	if(solver->value(*tch)==l_Undef){
        		loopf[0] = Lit(*tch,true); Clause* c = Clause_new(loopf, true);
				solver->addLearnedClause(c);
				solver->setTrue(loopf[0], c);
				if (verbosity>=2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
        	}
        }
    }
    return NULL;
}

/* Precondition:  !seen[i] for each i.
 * Postcondition: seen[i]  for exactly those i that are ancestors of cs in sp_justification. If defn_search==stop_at_cs, there should not be other cycle sources then cs in the path from added literals to cs.
 */
void IDSolver::markNonJustified(Var cs, vec<Var>& tmpseen) {
	Queue<Var> q;
	markNonJustifiedAddParents(cs, cs, q, tmpseen);
	// Now recursively do the same with each enqueued Var.
	Var x;
	while (q.size() > 0) {
		x = q.peek();
		q.pop();
		markNonJustifiedAddParents(x, cs, q, tmpseen);
	}
}

inline void IDSolver::markNonJustifiedAddVar(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
	if (!seen[v] && (scc[v] == scc[cs]) && (defn_search == include_cs || v == cs || !isCS[v])) {
		seen[v] = 1;
		tmpseen.push(v);
		q.insert(v);
		//total_marked_size++;
	}
}

void IDSolver::markNonJustifiedAddParents(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
	vec<Var>& v = disj_occurs[x + x];
	for (int i = 0; i < v.size(); ++i){
		if (var(sp_justification_disj[v[i]]) == x){
			markNonJustifiedAddVar(v[i], cs, q, tmpseen);
		}
	}
	vec<Var>& w = conj_occurs[x + x];
	for (int i = 0; i < w.size(); i++){
		markNonJustifiedAddVar(w[i], cs, q, tmpseen);
	}
	if (aggsolver!=NULL) {
		vec<Var> heads;
		aggsolver->getHeadsOfAggrInWhichOccurs(x, heads);
		for(int i=0; i<heads.size(); i++){
			vec<Lit>& jstfc = sp_justification_aggr[heads[i]];
			for (int k=0; k < jstfc.size(); k++){
				if(jstfc[k] == Lit(x, false)){ // Found that x is actually used in y's justification.
					markNonJustifiedAddVar(heads[i], cs, q, tmpseen);
					break;
				}
			}
		}
	}
}

inline void IDSolver::apply_changes() {
    for (int i=changed_vars.size()-1; i>=0; i--) {
        Var v = changed_vars[i];
        if (!seen[v]) {
            if (getDefType(v)==DISJ) cf_justification_disj[v] = sp_justification_disj[v];
            else {
                assert(getDefType(v)==AGGR);
                vec<Lit>& sp = sp_justification_aggr[v];
                vec<Lit>& cf = cf_justification_aggr[v];
                cf.clear();
                for (int j=0; j<sp.size(); ++j) cf.push(sp[j]);
            }
            seen[v]=1;
        }
    }
    for (int i=0; i<changed_vars.size(); i++)
    	seen[changed_vars[i]]=0;
    changed_vars.clear();
}

inline void IDSolver::clear_changes() {
    for (int i=changed_vars.size()-1; i>=0; i--) {
        Var v = changed_vars[i];
        if (!seen[v]) {
            if (getDefType(v)==DISJ) sp_justification_disj[v] = cf_justification_disj[v];
            else {
                assert(getDefType(v)==AGGR);
                vec<Lit>& sp = sp_justification_aggr[v];
                vec<Lit>& cf = cf_justification_aggr[v];
                sp.clear();
                for (int j=0; j<cf.size(); ++j) sp.push(cf[j]);
            }
        }
    }
    for (int i=0; i<changed_vars.size(); i++)
    	seen[changed_vars[i]]=0;
    changed_vars.clear();
}

/*********************
 * AGGSOLVER METHODS *
 *********************/

vec<Lit>& IDSolver::getCFJustificationAggr(Var v){
	return cf_justification_aggr[v];
}

void IDSolver::cycleSourceAggr(Var v, vec<Lit>& nj, bool becamecyclesource){
	change_jstfc_aggr(v,nj);
	for(int i=0; i<nj.size(); i++){
		if(becamecyclesource && isDefInPosGraph(var(nj[i])) && scc[v] == scc[var(nj[i])]){
			addCycleSource(v);
			break;
		}
	}
}

void IDSolver::notifyAggrHead(Var head){
	defdVars.push(head);
	assert(!isDefInPosGraph(head));
	definition[head]->setType(AGGR);
}

//=================================================================================================
// Debug + etc:
// a literal is a variable shifted one to the left
// a variable is a literal shifted one to the right

inline void IDSolver::printLit(Lit l){
    solver->printLit(l);
}


template<class C>
inline void IDSolver::printClause(const C& c){
    solver->printClause(c);
}

inline void IDSolver::printRule(const Rule& c){
    for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}

/**
 * For debugging purposes, not for recursive aggregates (yet).
 */
bool IDSolver::isCycleFree() {
    assert(aggsolver==NULL);

    reportf("Showing cf- and sp-justification for disjunctive atoms. <<<<<<<<<<\n");
    for (int i = 0; i < nVars(); i++) {
        if (getDefType(i)==DISJ) {
            printLit(Lit(i,false)); reportf(" <- ");
            printLit(cf_justification_disj[i]);
            reportf("(cf); ");
            printLit(sp_justification_disj[i]);
            reportf("(sp)\n");
        }
    }
    reportf(">>>>>>>>>>\n");

    // Verify cycles.
    vec<int> isfree; // per variable. 0 = free, >0 = number of literals in body still to be justified.
    vec<Lit> justified;
    int cnt_nonjustified = 0;
    for (int i=0;i<nVars();++i) {
        justified.push(Lit(i,true)); // negative literals are justified anyhow.
        if (!isDefInPosGraph(i)) {
            isfree.push(0);
            justified.push(Lit(i,false));
        } else {
            ++cnt_nonjustified;
            isfree.push(getDefType(i)==CONJ ? (definition[i]->size()-1) : 1);
        }
    }
    assert(cnt_nonjustified>0);

    int idx=0;
    while (cnt_nonjustified>0 && idx<justified.size()) {
        Lit l = justified[idx++];

        // Occurrences as justifying literal.
        vec<Var>& ds = disj_occurs[toInt(l)];
        vec<Var>& cs = conj_occurs[toInt(l)];

        for (int i=0;i<ds.size();++i) {
            Var d = ds[i];
            if (cf_justification_disj[d]==l) {
                assert(isfree[d]==1);
                isfree[d]=0;
                justified.push(Lit(d,false));
                --cnt_nonjustified;
            }
        }
        for (int i=0;i<cs.size();++i) {
            Var c = cs[i];
            isfree[c]--;
            if (isfree[c]==0) {
                justified.push(Lit(c,false));
                --cnt_nonjustified;
            }
        }
    }

    if (cnt_nonjustified>0) {
        reportf("WARNING: There remain %d literals non-justified.\n",cnt_nonjustified);

        vec<bool> printed; printed.growTo(nVars(),false);
        int i=0;
        while (i<nVars()) {
            reportf("Cycle:\n");
            for (;i<nVars() && (!isDefInPosGraph(i) || isfree[i]==0);i++) ;
            if (i<nVars()) {
                vec<Var> cycle;
                cycle.push(i);
                int idx=0;
                while (idx<cycle.size()) {
                    Var v = cycle[idx++];
                    if (getDefType(v)==DISJ) {
                        reportf("D %d justified by ",v+1); printLit(cf_justification_disj[v]); reportf(".\n");
                        if (!printed[var(cf_justification_disj[v])])
                            cycle.push(var(cf_justification_disj[v]));
                    } else {
                        reportf("C %d has",v+1);
                        Rule& c = *definition[v];
                        for (int j=0; j<c.size(); j++) {
                            Var vj = var(c[j]);
                            if (c[j]!=Lit(v,false) && sign(c[j]) && (isfree[vj]!=0 || printed[vj])) {
                                reportf(" %d",vj+1);
                                if (!printed[vj])
                                    cycle.push(vj);
                            }
                        }
                        reportf(" in its body.\n");
                    }
                    printed[v]=true;
                }
                for (int j=0;j<cycle.size();j++)
                    isfree[cycle[j]]=0;
            }
        }
    } else
        reportf("OK; cf_justification is cycle free.\n");
    return cnt_nonjustified==0;
}

/****************************
 * WELL FOUNDED MODEL CHECK *
 ****************************/

/**
 * FIXME het onderstaande is momenteel niet te implementeren, omdat het steunt op een juiste versie van de datastructuren
 * defType en definition, maar het probleem is dat die zijn opgesteld in functie van loops in de POSITIEVE dependency
 * graph, dus wat hier nu uitkomt is nonsense
 */

bool IDSolver::isWellFoundedModel() {
	return true;
	wfroot = vector<Var>(nVars(), 0);
	wfvisited = vector<int>(nVars(), 0);
	wfcounters = vector<int>(nVars(),0);
	wfisMarked = vector<bool>(nVars(),false);
	wfvisitNr = 1;

	findMixedCycles();
	if(wfmixedCycleRoots.empty()) return true;

	markUpward();
	wffixpoint = false;

	/**
	* until full fixpoint
	* 	pas de TP operator toe tot fixpoint
	* 	hou een ondergrens en een bovengrens bij, voor de certainly true en de certainly false
	* 	maak een gepaste onderschatting voor de negative unknown literals
	* 	wat dan wordt afgeleid is certainly true
	* 	maak een overschatting voor de negatieve unknown literals
	* 	wat niet wordt afgeleid is certainly false
	* 	kijk of full fixpoint reached, anders begin opnieuw
	*/
	while(!wffixpoint) {
		wffixpoint = true;

		initializeCounters();
		forwardPropagate(true);
		if(wfmarkedAtoms.empty()){
			return true;
		}
		overestimateCounters();
		forwardPropagate(false);
		removeMarks();
		if(wfmarkedAtoms.empty()){
			return true;
		}
	}

	return false;
}

void IDSolver::mark(Lit l) {
   wfisMarked[toInt(l)] = true;
   wfmarkedAtoms.insert(l);
}

void IDSolver::markUpward() {
	for(vector<int>::size_type n = 0; n < wfmixedCycleRoots.size(); ++n) {
		Var temp = wfmixedCycleRoots[n];
		Lit root = Lit(temp, temp<0);
		wfqueuePropagate.push(root);
		mark(root);
	}

	while(!wfqueuePropagate.empty()) {
		Lit l = wfqueuePropagate.front();
		wfqueuePropagate.pop();

		assert(value(l)==l_False);

		// true conjuntions with ~defLitp in the body
		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			if(value(head)==l_True){
				if(!wfisMarked[head]) {
					wfqueuePropagate.push(Lit(head, false));
					mark(Lit(head, false));
				}
			}
		}

		// true disjunctions and false conjunctions where l is the direct justification watch
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			Lit just = cf_justification_disj[head];
			if(value(head)==l_True && just==l){
				Lit h = Lit(head, true);	//FIXME dit steunt eigenlijk allemaal op hoe het in de completion is opgeslagen, dus dit allemaal aanpassen
				if(!wfisMarked[toInt(h)]) {
					wfqueuePropagate.push(h);
					mark(h);
				}
			}
		}
		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			int f = 0; //there are no justifications for conjunctions, so take the first false element encountered.
			for(; f<definition[head]->size(); f++){
				Lit just = definition[head]->operator [](f);
				if(value(just)==l_False){
					break;
				}
			}
			if(f==definition[head]->size()){
				continue;
			}
			Lit just = definition[head]->operator [](f);
			if(just==l){
				Lit h = Lit(head, true);
				if(!wfisMarked[toInt(h)]) {
					wfqueuePropagate.push(h);
					mark(h);
				}
			}
		}
		// false disjunctions with defLitp in the body
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			if(value(head)==l_False){
				if(!wfisMarked[head]) {
					wfqueuePropagate.push(Lit(head, false));
					mark(Lit(head, false));
				}
			}
		}
	}
}

/**
 * Visit the heads of all rules and check the current justification for loops with mixed signs (because of standard propagation,
 * there are no other loops). The head is always positive, so pure negative loops are not possible.
 */
void IDSolver::findMixedCycles() {
	for(int i=0; i<defdVars.size(); i++){
		Var v = defdVars[i];
		if(definition[v]->size()>0){
			if(!wfvisited[v]){
				visitWF(v, true);
			}
		}
	}
}

/**
 * NOTE: do not use the NONDEF type, because NONDEF only means there is no POSITIVE loop positive in the definition
 */
//FIXME currently no well founded model checking over aggregates
void IDSolver::visitWF(Var v, bool pos) {
	wfroot[v] = v;
	wfvisited[v] = wfvisitNr;
	wfvisitNr++;
	wfstack.push(pos?v:-v);	//if the visit was through a negative literal, the negation of v is pushed

	assert(getDefType(v)!=AGGR);

	bool headtrue = value(Lit(v, false))==l_True;

	//head is false and disj, or head is true and conj: use all body literals to check for justification
	//value is false: use all body literals as justification if DISJ, only one if CONJ
	if((headtrue && getDefType(v)==CONJ) || (!headtrue && getDefType(v)==DISJ)){
		for(int i=0; i<definition[v]->size(); i++){
			Lit l = definition[v]->operator [](i);
			Var w = var(l);
			if(definition[w]!=NULL){
				if(wfvisited[w]==0){
					visitWF(w, !sign(l));
				}
				if(wfvisited[w]>0 && wfvisited[w]<wfvisited[v]){ //not in component and visited earlier
					wfroot[v] = wfroot[w];
				}
			}
		}
	}else{//head is true and DISJ or head is false and CONJ: for DISJ, just check its one justification
			// for a CONJ, randomly check one of the false literals. If there is no loop through it, problem solved.
			//			If there is, it will be found later if another false literal exists without a mixed loop.
		if(getDefType(v)==CONJ){
			for(int i=0; i<definition[v]->size(); i++){
				Lit l = definition[v]->operator [](i);
				Var w = var(l);
				if(definition[w]!=NULL && value(l)==l_True){ //l_True because body literals have inverted sign in conj
					for(int z=0; z<wfvisited.size(); z++){
						reportf("%d ", wfvisited[z]);
					}
					reportf(", and checking for %d\n", w);
					if(wfvisited[w]==0){
						visitWF(w, !sign(l));
					}
					if(wfvisited[w]>0 && wfvisited[w]<wfvisited[v]){ //not in component and visited earlier
						wfroot[v] = wfroot[w];
					}
					break;
				}
			}
		}else{
			Lit l = cf_justification_disj[v];
			Var w = var(l);
			if(definition[w]!=NULL){
				if(wfvisited[w]==0){
					visitWF(w, !sign(l));
				}
				if(wfvisited[w]>0 && wfvisited[w]<wfvisited[v]){ //not in component and visited earlier
					wfroot[v] = wfroot[w];
				}
			}
		}
	}

	if(wfroot[v] == v) {
		bool mixedComponent = false;
		int w = 0;

		while(v != w) {
			w = wfstack.top();
			wfstack.pop();
			wfvisited[w] = -1; // -1 indicates that the atom is in a component.
			if(  (v < 0 && w > 0) || (v > 0 && w < 0) ){ // v and w have a different sign.
				mixedComponent = true;
			}
		}
		if(mixedComponent){
			wfmixedCycleRoots.push_back(v);
		}
	}
}

/**
 * Initializes the body counter of the rules on the number of marked atoms. If any atom is false, it is pushed on the queue
 */
void IDSolver::initializeCounters() {
	for(set<Lit>::iterator i=wfmarkedAtoms.begin(); i!=wfmarkedAtoms.end(); i++){
		int n=0;
		Var v = var(*i);
		for(int j=0; j<definition[v]->size(); j++){
			Lit bl = definition[v]->operator [](j);
			if(wfisMarked[var(bl)]){
				n++;
			}else if((getDefType(v)==DISJ && value(bl)==l_False) || (getDefType(v)==CONJ && value(bl)==l_True)) {
				wfqueuePropagate.push(bl);
				break;
			}
		}
		wfcounters[v] = n;
	}
}

void IDSolver::forwardPropagate(bool removemarks) {
	while(!wfqueuePropagate.empty()) {
		Lit l = wfqueuePropagate.front();
		wfqueuePropagate.pop();

		if(!wfisMarked[var(l)]){
			continue;
		}

		wfisMarked[var(l)] = false;
		if(removemarks) {
			wfmarkedAtoms.erase(l);
			wffixpoint = false;
		}

		assert(value(l)==l_False);

		//update head counters when the LITERAL occurs in the body -> substract one because literal became false
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			if(--wfcounters[head]==0){
				wfqueuePropagate.push(Lit(head, false));
			}
		}
		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			if(--wfcounters[head]==0){
				wfqueuePropagate.push(Lit(head, false));
			}
		}

		l = ~l;
		//-l became true, so if a head of a rule in which -l is a body literal is marked, push its negation on the queue and set the counter to 0
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			if(wfisMarked[head]) {
				wfqueuePropagate.push(Lit(head, true));
				wfcounters[head] = 0;
			}
		}
		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			if(wfisMarked[head]) {
				wfqueuePropagate.push(Lit(head, true));
				wfcounters[head] = 0;
			}
		}
	}
}


void IDSolver::overestimateCounters() {
	for(set<Lit>::iterator i=wfmarkedAtoms.begin(); i!=wfmarkedAtoms.end(); i++){
		Lit markedl = *i;
		assert(wfcounters[toInt(markedl)] > 0);

		if(getDefType(var(markedl))==CONJ) {
			for(int j=0; j<definition[var(markedl)]->size(); j++) {
				Lit bl = definition[var(markedl)]->operator [](j);
				if(wfcounters[toInt(bl)]!=0 && !sign(bl)) {
					if((--wfcounters[toInt(markedl)])==0){
						wfqueuePropagate.push(markedl);
					}
				}
			}
		}else {
			for(int j=0; j<definition[var(markedl)]->size(); j++) {
				Lit bl = definition[var(markedl)]->operator [](j);
				if(wfcounters[toInt(bl)]!=0 && sign(bl)) {
					wfqueuePropagate.push(markedl);
					wfcounters[toInt(markedl)] = 0;
				}
			}
		}
	}
}

/**
 * Removes all elements from the marked stack that are already marked and removes their mark
 * Sets all elements marked that are on the stack but not marked at the moment
 */
void IDSolver::removeMarks() {
	stack<Lit> temp;
	for(set<Lit>::iterator i=wfmarkedAtoms.begin(); i!=wfmarkedAtoms.end(); i++){
		Lit markedl = *i;
		if(wfisMarked[toInt(markedl)]) {
			assert(sign(markedl));
			temp.push(markedl);
			wfisMarked[toInt(markedl)] = false;
			wffixpoint = false;
		}else {
			wfisMarked[toInt(markedl)] = true;
		}
	}
	while(!temp.empty()) {
		wfmarkedAtoms.erase(temp.top());
		temp.pop();
	}
}


//TARJAN ALGORITHM FOR FINDING UNFOUNDED SETS IN GENERAL INDUCTIVE DEFINITIONS (NOT ONLY SINGLE CONJUNCTS). THIS DOES NOT WORK YET
///////////////
////Finding unfounded checks by
////Generalized tarjanUFS
////DOES NOT WORK WITH AGGREGATES
////justification is een subgrafe van de dependency grafe
//UFS IDSolver::visitForUFSgeneral(Var v, Var cs, std::set<Var>& ufs, int visittime, vec<Var>& stack, vec<Var>& root, vec<Var>& visited, vec<bool>& incomp){
//	visited[v]=visittime;visittime++;root[v]=v;
//
//	DefType type = defType[v];
//
//	if(type==AGGR){return OLDCHECK;}
//	assert(type==CONJ || type==DISJ);
//
//	Clause* c = definition[v];
//	//Rule* c = definition[v];
//
//	for(int i=0; i<c->size(); i++){
//		DefType childtype = defType[var(c->operator [](i))];
//		Lit l = c->operator [](i);
//		if(var(l)==v){ continue; } //rule head or identical body atom
//		if(childtype==AGGR){return OLDCHECK;}
//		if(childtype==NONDEF || scc[var(l)]!=scc[v] || incomp[var(l)] /*|| STILL JUSTIFIED*/){
//			if(value(l)!=l_False && type==DISJ){
//				incomp[v]=true;
//				//change_jstfc_disj(v, l);
//				return NOTUNFOUNDED;
//			}
//		}
//	}
//
//	stack.push(v);
//
//	int notunfoundedchildren = 0;
//	int totaldefined = 0;
//	bool notunfounded = false, stop = false;
//
//	for(int i=0; i<c->size(); i++){
//		Var child = var(c->operator [](i));
//		if(child==v){continue;}
//		if(!(defType[child]==CONJ || defType[child]==DISJ)){continue;}
//		totaldefined++;
//		if(visited[child]==-1){
//			switch(visitForUFSgeneral(child, cs, ufs, visittime, stack, root, visited, incomp)){
//			case STILLPOSSIBLE:
//				//if CONJ and the child's parent was visited earlier than this node,
//				//then return higher, because no other conjunct has to be visited to find a UFS if the loop goes higher
//				//if this is the highest visited node, there is a loop which starts here so UFS, so stop
//				if(type==CONJ){
//					if(visited[root[child]]<visited[v]){
//						return STILLPOSSIBLE;
//					}else if(visited[root[child]]==visited[v]){
//						stop = true;
//					}
//				}
//				break;
//			case NOTUNFOUNDED:
//				if(type == CONJ){
//					notunfoundedchildren++;
//				}else{
//					//change_jstfc_disj(v, c->operator [](i));
//					notunfounded = true;
//				}
//				break;
//			case UFSFOUND:
//				return UFSFOUND;
//			case OLDCHECK:
//				return OLDCHECK;
//			}
//		}
//		if(notunfounded || stop){
//			break;
//		}
//		if(!incomp[child] && visited[root[child]]<visited[v]){
//			root[v]=root[child];
//		}
//	}
//
//	if(type == CONJ && notunfoundedchildren==totaldefined){
//		notunfounded = true;
//		//do something with justifications for CONJ, or not necessary?
//	}
//
//	if(notunfounded){
//		//change justification of this node and of anything above x on the stack
//		Var x = stack.last();
//		while(x!=v){
//			incomp[x]=true;
//			/*if(defType[x]==DISJ){
//				//change the justification randomly to one of the body literals CHECK IF THIS IS CORRECT
//				Queue<Var> q;
//				Justify(v, cs, ufs, q);
//			}*/
//			stack.pop();
//			x=stack.last();
//		}
//
//		return NOTUNFOUNDED;
//	}else {
//		if(root[v]==v){
//			bool allfalse = true;
//
//			Var x;
//			do{
//				x = stack.last();
//				if(value(x)!=l_False){allfalse = false;}
//				ufs.insert(x);
//				incomp[x]=true;
//				stack.pop();
//			}while(x!=v);
//
//			if(allfalse){
//				ufs.clear();
//				return STILLPOSSIBLE;
//			}
//			if(ufs.size()>1){
//				return UFSFOUND;
//			}else{
//				int containsx = 0;
//				for(int i=0; i<c->size(); i++){
//					if(x==var(c->operator [](i))){
//						containsx++;
//					}
//				}
//				if(containsx>1){ //there is a loop of length 1, so x itself is an UFS
//					return UFSFOUND;
//				}else{//no loops, x is only an SCC, not a UFS
//					ufs.clear();
//					return STILLPOSSIBLE;
//				}
//			}
//		}else{
//			return STILLPOSSIBLE;
//		}
//	}
//}
//
////makes each literal (or its negation) that has recently been assigned into a cycle source if it occurs in a disjunctive rule
//void IDSolver::findCycleSources() {
//	clearCycleSources();
//	clear_changes();
//
//	//ADDED LAST PART FOR CONSISTENCY
//	if (prev_conflicts == solver->conflicts && defn_strategy == always && solver->decisionLevel()!=0) {
//		for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
//			Lit x = solver->getRecentAssignments(i);
//			if(value(x)==l_True){
//				x = ~x;
//			}
//			for(int j=0; j<disj_occurs[toInt(x)].size(); j++) {
//				Var v = disj_occurs[toInt(x)][j];
//				if(defType[v]==CONJ || defType[v]==DISJ || defType[v]==AGGR){
//					addCycleSource(v);
//				}
//			}
//		}
//	} else {
//		for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
//			Lit x = solver->getRecentAssignments(i);
//			if(value(x)==l_True){
//				x = ~x;
//			}
//			for(int j=0; j<disj_occurs[toInt(x)].size(); j++) {
//				Var v = disj_occurs[toInt(x)][j];
//				if(defType[v]==CONJ || defType[v]==DISJ || defType[v]==AGGR){
//					addCycleSource(v);
//				}
//			}
//		}
//	}
//}


/* Code that maarten already commented. No idea what it does.
 (@&) if there is but one remaining non-false literal with weight <= ae.max, that literal has to be made true.
 Lit candidate; bool use_candidate=true;
 for (int u=0;confl==NULL && u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight<=ae.max) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));

 as.set[as.max].weight <= ae.max and there is but one non-false literal with weight < ae.min, that literal has to become true.
 if (as.max<=ae.max) {
 Lit candidate; bool use_candidate=true;
 for (int u=0;u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight<ae.min) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));
 }

 if there is but one remaining non-false literal with weight >= ae.min, that literal has to be made true.
 Lit candidate; bool use_candidate=true;
 for (int u=0;confl==NULL && u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight>=ae.min) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));

 as.set[as.max].weight <= ae.max and there is but one non-false literal with weight < ae.min, that literal has to become true.
 if (as.min>=ae.min) {
 Lit candidate; bool use_candidate=true;
 for (int u=0;u<as.set.size();u++) {
 if (use_candidate && value(as.set[u].lit)!=l_False && as.set[u].weight>ae.max) {
 if (candidate!=lit_Undef)
 use_candidate=false;
 else
 candidate=as.set[u].lit;
 }
 }
 if (use_candidate && candidate!=lit_Undef && value(candidate)==l_Undef)
 aggrEnqueue(candidate,new AggrReason(&ae,&as,POS));
 }
 */
