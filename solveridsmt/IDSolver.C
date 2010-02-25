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
	posloops(true), negloops(true),
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
	justification.clear();
	justification.growTo(nVars());

	// initialize nb_body_lits_to_justify
	vec<Var> usedseen;
	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (isFalse(v)){
			continue;
		}
		switch (getDefType(v)) {
		case DISJ:
		case AGGR:
			seen[v] = 1;
			break;
		case CONJ:
			seen[v] = definition[v]->size();
			break;
		default:
			assert(false);
		}
		usedseen.push(v);
	}

	// initialize a queue of literals that are safe with regard to cycle-freeness. (i.e.: either are not in justification, or are justified in a cycle-free way.)
	vec<Lit> propq;
	for (int i = 0; i < nVars(); ++i){
		Lit l = createNegativeLiteral(i);
		if (!isFalse(l)){
			propq.push(l); // First negative literals are added that are not already false
		}
		l = createPositiveLiteral(i);
		if (!isDefInPosGraph(i) && !isFalse(l)){
			propq.push(l); // Then all non-false non-defined positive literals.
		}
	}

	// propagate safeness to defined literals until fixpoint.
	// While we do this, we build the initial justification.
	while (propq.size() > 0) {
		Lit l = propq.last(); //only heads are added to the queue
		propq.pop();

		vec<Lit> heads;
		vec<vec<Lit> > jstf;
		propagateJustificationDisj(l, jstf, heads);
		propagateJustificationConj(l, jstf, heads);
		propagateJustificationAggr(l, jstf, heads);

		for(int i=0; i<heads.size(); i++){
			changejust(var(heads[i]), jstf[i]);
			propq.push(heads[i]);
		}
	}

	// vars v that still have nb_body_lits_to_justify[v]>0 can never possibly become true: make them false.
	if(verbosity > 2){
		reportf("Initialization of justification makes these atoms false: [");
	}

	/**
	 * Goes through all definitions and checks whether they can still become true (if they have been justified).
	 * Otherwise, it is checked (overestimation) whether a negative loop might be possible. If this is not the case, the definition is removed
	 * from the data structures.
	 */
	vec<Var> reducedVars;
	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (seen[v] > 0) {
			if(verbosity >= 2){ reportf(" %d",v+1); }
			if(isTrue(v)){
				throw theoryUNSAT;
			}else if(isUnknown(v)){
				solver->setTrue(createNegativeLiteral(v), NULL);
			}

			if(defOcc[v]==POSLOOP){
				defOcc[v] = NONDEFOCC;
				definition[v] = NULL;
				defType[v] = NONDEFTYPE;
			}else{
				defOcc[v] = MIXEDLOOP;
				reducedVars.push(v);
			}
			--atoms_in_pos_loops;
		}else{
			reducedVars.push(v);
		}
	}
	defdVars.clear();
	reducedVars.copyTo(defdVars);

	for(int i=0; i<usedseen.size(); i++){
		seen[usedseen[i]] = 0;
	}

	if (verbosity >= 2){
		reportf(" ]\n");
	}

	if (atoms_in_pos_loops == 0){
		posloops = false;
	}

	if(!posloops && !negloops){
		solver->setIDSolver(NULL);
		if(aggsolver!=NULL){
			aggsolver->setIDSolver(NULL);
		}
		if (verbosity >= 1){
			reportf("| All recursive atoms falsified in initializations.                           |\n");
		}
	}

	if(verbosity > 1){
		for(int i=0; i<defdVars.size(); i++){
			Var w = defdVars[i];
			switch(defOcc[w]){
			case NONDEFOCC:	reportf("%d=NONDEFOCC, ", w); break;
			case MIXEDLOOP:	reportf("%d=MIXEDLOOP, ", w); break;
			case BOTHLOOP:	reportf("%d=BOTHLOOP, ", w); break;
			case POSLOOP:	reportf("%d=POSLOOP, ", w); break;
			}
		}
	}

#ifdef DEBUG
	for(int i=0; i<defdVars.size(); i++){
		assert(justification[defdVars[i]].size()>0 || defType[defdVars[i]]==CONJ);
	}
#endif

	return true;
}

/**
 * propagate the fact that w has been justified.
 *
 * Return all newly justified head in heads
 * Return all justification of those justified heads in jstf
 * Adapt nb_body... when some element has been justified
 */
void IDSolver::propagateJustificationDisj(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads){
	for (int i = 0; i < disj_occurs[toInt(l)].size(); ++i) {
		Var v = (disj_occurs[toInt(l)])[i];
		if (isFalse(v) || seen[v] == 0){
			continue;
		}
		seen[v] = 0;
		heads.push(createPositiveLiteral(v));
		jstf.push();
		jstf.last().push(l);
	}
}

void IDSolver::propagateJustificationConj(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads){
	for (int i = 0; i < conj_occurs[toInt(l)].size(); ++i) {
		Var v = (conj_occurs[toInt(l)])[i];
		if (isFalse(v) || seen[v] == 0){
			continue;
		}
		seen[v]--;
		if (seen[v] == 0){
			heads.push(createPositiveLiteral(v));
			jstf.push();
		}
	}
}

void IDSolver::propagateJustificationAggr(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads){
	if (aggsolver==NULL) {
		return;
	}
	aggsolver->propagateJustifications(l, jstf, heads, seen);
}

void IDSolver::notifyVarAdded(){
	seen.growTo(nVars(), 0);
	//seen2.push(0);

	definition.growTo(nVars(), NULL);
	defType.growTo(nVars(), NONDEFTYPE);
	defOcc.growTo(nVars(), NONDEFOCC);
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
	assert(isPositive(ps[0]));

	if (ps.size() == 1) {
		Lit head = conj?ps[0]:~ps[0]; //empty set conj = true, empty set disj = false
		if (isFalse(head)){
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
		defType.growTo(nVars(), NONDEFTYPE);
		defOcc.growTo(nVars(), NONDEFOCC);
		defType[var(ps[0])]=conj?CONJ:DISJ;
		//defOcc is initialized when finishing the datastructures
		definition[var(ps[0])] = r;

		//create the completion
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

/*
 * Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
 *
 * @PRE: aggregates have to have been finished
 */
bool IDSolver::finishECNF_DataStructures() {
	init = false;
	defType.growTo(nVars(), NONDEFTYPE);
	defOcc.growTo(nVars(), NONDEFOCC);

	if (verbosity >= 1){reportf("| Number of rules           : %6d                                          |\n",defdVars.size()); }

	// Initialize scc of full dependency graph
	scc.growTo(nVars(), -1);
	vec<bool> incomp(nVars(), false);
	vec<Var> stack;
	vec<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	vec<Var> rootofmixed;
	vec<Var> nodeinmixed;
	int counter = 1;

	for (int i=0; i<defdVars.size(); i++){
		if (visited[defdVars[i]]==0){
			visitFull(defdVars[i],scc,incomp,stack,visited,counter,true,rootofmixed, nodeinmixed);
		}
	}

	if(verbosity >= 3){
		reportf("Printing sccs full graph:");
		for (int i=0; i<nVars(); i++){
			reportf("SCC of %d is %d\n", i, scc[i]);
		}
		reportf("Ended printing sccs. Size of roots = %d, nodes in mixed = %d.\n", rootofmixed.size(), nodeinmixed.size());
	}

	//all var in rootofmixed are the roots of mixed loops. All other are no loops (size 1) or positive loops

	// Initialize scc of positive dependency graph
	for (int i=0; i<nodeinmixed.size(); i++){
		incomp[nodeinmixed[i]]=false;
		defOcc[nodeinmixed[i]]=MIXEDLOOP;
		visited[nodeinmixed[i]]=0;
	}
	stack.clear();
	counter = 1;

	for (int i=0; i<nodeinmixed.size(); i++){
		if (visited[nodeinmixed[i]]==0){
			visit(nodeinmixed[i],scc,incomp,stack,visited,counter);
		}
	}

	if(verbosity >= 3){
		reportf("Printing sccs pos graph:");
		for (int i=0; i<nVars(); i++){
			reportf("SCC of %d is %d\n", i, scc[i]);
		}
		reportf("Ended printing sccs.\n");
	}

	// Determine which literals should no longer be considered defined (according to the scc in the positive graph) + init occurs
	atoms_in_pos_loops = 0;
	disj_occurs.growTo(2 * nVars());
	conj_occurs.growTo(2 * nVars());
	Lit l;
	vec<Var> reducedVars;
	for (int i = 0; i < defdVars.size(); ++i) {
		Var v = defdVars[i];
		bool isdefd = false;
		switch (getDefType(v)) {
		case DISJ: {
			Rule& dfn = *definition[v];
			for (int j = 0; j < dfn.size(); ++j) {
				l = dfn[j];
				if (l != dfn.getHeadLiteral()){ //don't look for a justification that is the head literal itself
					disj_occurs[toInt(l)].push(v);
				}
				if (isPositive(l) && inSameSCC(v, var(l))){
					isdefd = true;
				}
			}
			break;
		}
		case CONJ: {
			Rule& dfn = *definition[v];
			for (int j = 0; j < dfn.size(); ++j) {
				l = dfn[j];
				if (l != dfn.getHeadLiteral()){ //don't look for a justification that is the head literal itself
					conj_occurs[toInt(l)].push(v);
				}
				if (isPositive(l) && inSameSCC(v, var(l))){
					isdefd = true;
				}
			}
			break;
		}
		case AGGR: {
			if(aggsolver!=NULL){
				vector<WLV>& lits = aggsolver->getLiteralsOfAggr(i);
				for (vector<int>::size_type j = 0; !isdefd && j < lits.size(); ++j){
					if (inSameSCC(v, var(lits[j].lit))){ // NOTE: disregard sign here: set literals can occur both pos and neg in justifications. This could possibly be made more precise for MIN and MAX...
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
			reducedVars.push(v);
			defOcc[v]=defOcc[v]==MIXEDLOOP?BOTHLOOP:POSLOOP;
		}else{
			if(defOcc[v]==NONDEFOCC){
				definition[v] = NULL;
				defType[v] = NONDEFTYPE;
			}else if(defOcc[v]==MIXEDLOOP){
				reducedVars.push(v);
			}
		}
	}
	defdVars.clear();
	reducedVars.copyTo(defdVars);

	if(atoms_in_pos_loops==0){
		posloops = false;
	}
	if(rootofmixed.size()==0){
		negloops = false;
	}

	if (verbosity >= 1){
		reportf("| Number of recursive atoms in positive loops : %6d                        |\n",(int)atoms_in_pos_loops);
		if(negloops){
			reportf("| Mixed loops also exist                                                  |\n");
		}
	}

	if (!negloops && !posloops) {
		return false;
	}

	isCS.growTo(nVars(), false);

	if(verbosity > 1){
		for(int i=0; i<defdVars.size(); i++){
			Var w = defdVars[i];
			switch(defOcc[w]){
			case NONDEFOCC:	reportf("%d=NONDEFOCC, ", w); break;
			case MIXEDLOOP:	reportf("%d=MIXEDLOOP, ", w); break;
			case BOTHLOOP:	reportf("%d=BOTHLOOP, ", w); break;
			case POSLOOP:	reportf("%d=POSLOOP, ", w); break;
			}
		}
	}

	return true;
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the FULL dependency graph
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visitFull(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter, bool throughPositiveLit, vec<int>& rootofmixed, vec<Var>& nodeinmixed) {
	assert(!incomp[i]);
	assert(isDefined(i));
	++counter;
	visited[i] = throughPositiveLit?counter:-counter;
	root[i] = i;
	stack.push(i);

	switch (getDefType(i)) {
	case DISJ:
	case CONJ:{
		for (int j = 0; j < definition[i]->size(); ++j) {
			Lit l = (*definition[i])[j];
			int w = var(l);
			if(!isDefined(w)){
				continue;
			}
			if (visited[w]==0){
				visitFull(w,root,incomp,stack,visited,counter,isPositive(l),rootofmixed, nodeinmixed);
			}else if(!incomp[w] && !isPositive(l) && visited[i]>0){
				visited[i] = -visited[i];
			}
			if (!incomp[w] && abs(visited[root[i]])>abs(visited[root[w]])){
				root[i] = root[w];
			}
		}
		break;
	}
	case AGGR: {
		vector<WLV>& lits = aggsolver->getLiteralsOfAggr(i);
		for (vector<int>::size_type j = 0; j < lits.size(); ++j) {
			Var w = var(lits[j].lit);
			if(!isDefined(w)){
				continue;
			}
			if (visited[w]==0){
				visitFull(w,root,incomp,stack,visited,counter,true, rootofmixed, nodeinmixed);
			} else if(!incomp[w] && visited[i]>0){
				visited[i] = -visited[i];
			}
			if (!incomp[w] && abs(visited[root[i]])>abs(visited[root[w]])){
				root[i] = root[w];
			}
		}
		break;
	}
	default:
		assert(false);
	}

	if (root[i] == i) {
		vec<Var> scc;
		bool mixed = false;
		int w;
		do {
			w = stack.last();
			stack.pop();
			visited[w]<0?mixed=true:true;
			root[w] = i; //these are the found sccs
			scc.push(w);
			incomp[w] = true;
		} while (w != i);
		if(mixed){
			rootofmixed.push(i);
			for(int i=0; i<scc.size(); i++){
				nodeinmixed.push(scc[i]);
			}
		}
	}
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the
 * POSITIVE dependency graph.
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visit(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter) {
	assert(!incomp[i]);
	visited[i] = ++counter;
	root[i] = i;
	stack.push(i);

	switch (getDefType(i)) {
	case DISJ:
	case CONJ:{
		for (int j = 0; j < definition[i]->size(); ++j) {
			Lit l = (*definition[i])[j];
			Var w = var(l);
			if (isDefined(w) && i != w && isPositive(l)) {
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
		vector<WLV>& lits = aggsolver->getLiteralsOfAggr(i);
		for (vector<int>::size_type j = 0; j < lits.size(); ++j) {
			Var w = var(lits[j].lit);
			if (isDefined(w) && visited[w]==0){
				visit(w,root,incomp,stack,visited,counter);
			}
			if (!incomp[w] && visited[root[i]]>visited[root[w]]){
				root[i] = root[w];
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
			root[w] = i; //these are the found sccs
			incomp[w] = true;
		} while (w != i);
	}
}

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

 	if(ufs_strategy==breadth_first){
 		for (int j=0; !ufs_found && j < css.size(); j++){
			if(isCS[css[j]]){
				ufs_found = unfounded(css[j], ufs);
			}
		}
 	}else{
 		int visittime = 1;	//time at which NO node has been visited yet
 		vec<Var> stack;
 		seen2.growTo(nVars(), 0);
 		/* the seen2 variable is used to indicate:
 		 * 		that a value has been visited (and its number is the time at which it was visited
 		 * 		0 means not yet visited
 		 * 		a negative value means that it has been visited at the abs value and that it has
 		 * 		already received a valid justification
 		 */
 		for (int j=0; !ufs_found && j < css.size(); j++){//hij komt nooit in het geval dat hij iets op de stack moet pushen, altijd disj unfounded???
 			if(isCS[css[j]] && seen[css[j]]==0){
 				//om geen seen2 nodig te hebben, mag seen niet tegelijk gebruikt kunnen worden in unfounded()
 				vec<vec<Lit> > network;	//maps a node to a list of nodes that have visited the first one
										//as index, the visited time is used
 				network.growTo(visittime+1);
 				network[visittime].push(Lit(css[j]));
 				UFS ret = visitForUFSsimple(css[j], ufs, visittime, stack, seen2, network);
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
 		for (int i = 0; i < nVars(); i++) {
 			seen2[i] = 0;
		}
 	}

 	Clause* confl = NULL;
	if (ufs_found) {
		if (verbosity >= 2) {
			reportf("Found an unfounded set of size %d: {",ufs.size());
			for (std::set<Var>::iterator it = ufs.begin(); it != ufs.end(); ++it)
				reportf(" %d",*it+1);
			reportf(" }.\n");
		}
		if (defn_strategy == adaptive){
			adaption_current++; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
		}
		confl = assertUnfoundedSet(ufs);
	} else { // Found a witness justification.
		apply_changes();
	}

	assert(aggsolver!=NULL || isCycleFree());
	return confl;
}

/**
 * Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void IDSolver::findCycleSources() {
	clearCycleSources();

	if (prev_conflicts == solver->conflicts && defn_strategy == always && solver->getNbOfRecentAssignments()>0) {
		for(int i=0; i<solver->getNbOfRecentAssignments(); i++){
			Lit l = solver->getRecentAssignments(i); //l has become true, so find occurences of ~l

			vec<Var>& ds = disj_occurs[toInt(~l)];
			for (int j = 0; j < ds.size(); j++) {
				checkJustification(ds[j], ~l);
			}

			if(aggsolver!=NULL){
				vec<Var> heads;
				aggsolver->getHeadsOfAggrInWhichOccurs(var(~l), heads);

				for(int j=0; j<heads.size(); j++){
					checkJustification(heads[j], ~l);
				}
			}
		}
	} else {
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		prev_conflicts = solver->conflicts;
		for (int i = 0; i < defdVars.size(); i++) {
			if(defType[defdVars[i]]==DISJ || defType[defdVars[i]]==AGGR){
				checkJustification(defdVars[i]);
			}
		}
	}
	if (verbosity >= 2) {
		reportf("Indirect propagations. Verifying %d cycle sources:",css.size());
		for (int i = 0; i < css.size(); ++i){
			reportf(" %d",css[i]+1);
		}
		reportf(".\n");
	}
}

void IDSolver::checkJustification(Var head, Lit lbecamefalse){
	if(isCS[head]){
		return;
	}
	bool dependsonl = false;
	for(int i=0; !dependsonl && i<justification[head].size(); i++){
		if(justification[head][i]==lbecamefalse){
			dependsonl = true;
		}
	}
	if(!dependsonl){
		isCS[head] = false;
		return;
	}

	handlePossibleCycleSource(head);
}

void IDSolver::checkJustification(Var head){
    if(isCS[head] || value(head)==l_False){
		return;
	}

    bool dependsonfalse = false;
	for(int i=0; !dependsonfalse && i<justification[head].size(); i++){
		if(value(justification[head][i])==l_False){
			dependsonfalse = true;
		}
	}
	if(!dependsonfalse){
		isCS[head] = false;
		return;
	}

	handlePossibleCycleSource(head);
}

void IDSolver::handlePossibleCycleSource(Var head){
	if (!isFalse(head) && isDefInPosGraph(head)) {
		vec<Lit> jstf;
		bool external;
		if(defType[head]==DISJ){
			external = findJustificationDisj(head, jstf);
		}else{
			assert(defType[head]==AGGR);
			aggsolver->findJustificationAggr(head, jstf);
			external = true;
			for(int i=0; external && i<jstf.size(); i++){
				if(inSameSCC(head, var(jstf[i])) && isPositive(jstf[i])){
					external = false;
				}
			}
		}
		assert(jstf.size()>0);
		if(external){
			changejust(head, jstf);
		}else{
			addCycleSource(head);
		}
	}
}

/**
 * Looks for a justification for the given var. Attempts to find one that is not within the same positive dependency
 * graph scc (and certainly not false).
 * Return true if the justification is external
 */
bool IDSolver::findJustificationDisj(Var v, vec<Lit>& jstf) {
	Rule& c = *definition[v];
	bool externallyjustified = false;
	int pos = -1;
	for(int i=0; !externallyjustified && i<c.size(); i++){
		if(!isFalse(c[i])){
			if(!inSameSCC(v, var(c[i])) || !isPositive(c[i]) || defType[var(c[i])]==NONDEFTYPE){
				externallyjustified = true;
				pos = i;
			}else{
				pos = i;
			}
		}
	}
	if(pos>=0){
		jstf.push(c[pos]);
	}
	return externallyjustified;
}

/*
 * Return true if indirectpropagation is necessary. This is certainly necessary if the state is two-valued or if the strategy is always.
 */
bool IDSolver::indirectPropagateNow() {
	bool propagate = true;
	// if not always and state is three-valued.
	if (defn_strategy != always && solver->existsUnknownVar()){
		if (defn_strategy == lazy){
			propagate = false;
		}
		if (defn_strategy == adaptive && adaption_current < adaption_total) {
			adaption_current++;
			propagate = false;
		}
	}
	return propagate;
}

bool IDSolver::unfounded(Var cs, std::set<Var>& ufs) {
	//justify_calls++;
	vec<Var> tmpseen; // use to speed up the cleaning of data structures in "Finish"
	Queue<Var> q;
	Var v;

	markNonJustified(cs, tmpseen);
	bool csisjustified = false;

	seen[cs]=1; //no valid justification can be created just from looking at the body literals
	tmpseen.push(cs);

	q.insert(cs);
	ufs.clear();
	ufs.insert(cs);
	while (!csisjustified && q.size() > 0) {
		v = q.peek();
		q.pop();
		if (isJustified(v)){
			continue;
		}
		if (directlyJustifiable(v, ufs, q)){
			if (propagateJustified(v, cs, ufs)){
				csisjustified = true;
			}
		}
	}

	for (int i = 0; i < tmpseen.size(); i++) {
		seen[tmpseen[i]] = 0;
	}

#ifdef DEBUG
	for(int i=0; i<nVars(); i++){
		assert(seen[i]==0);
	}
#endif

	if(!csisjustified){
		assert(ufs.size() > 0); // The ufs atoms form an unfounded set. 'cs' is in it.
		return true;
	}else{
		ufs.clear();
		return false;
	}
}


/**
 * seen is used as a justification mark/counter:
 *
 * seen==0 || negative body literal <=> justified
 */
inline bool IDSolver::isJustified(Lit x){
	return isJustified(var(x)) || !isPositive(x);
}
inline bool IDSolver::isJustified(Var x){
	return seen[x]==0;
}

/**
 * Checks whether there is a justification for v given the current justification counters
 */
bool IDSolver::findJustificationDisj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	Rule& c = *definition[v];
	bool externallyjustified = false;
	currentjust[v]=1;
	int pos = -1;
	for(int i=0; !externallyjustified && i<c.size(); i++){
		if(c.getHeadLiteral()==c[i]){ continue;	}

		if (!isFalse(c[i])) {
            if (!isPositive(c[i]) || currentjust[var(c[i])]==0) {
            	if(!inSameSCC(v, var(c[i]))){
            		externallyjustified = true;
					pos = i;
				}else{
					pos = i;
				}
            } else{
            	nonjstf.push(var(c[i]));
            }
        }
	}
	if(pos>=0){
		jstf.push(c[pos]);
		currentjust[v]=0;
	}
	return currentjust[v]==0;
}

bool IDSolver::findJustificationConj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	Rule& c = *definition[v];
	currentjust[v]=0;
	for(int i=0; i<c.size(); i++){
		if(isPositive(c[i]) && currentjust[var(c[i])]!=0){
			currentjust[v]++;
			nonjstf.push(var(c[i]));
		}
	}
	return currentjust[v]==0;
}

bool IDSolver::findJustificationAggr(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust){
	currentjust[v] = 1; //used as boolean (0 is justified, 1 is not)
	if(aggsolver->directlyJustifiable(v, jstf, nonjstf, currentjust)){
		currentjust[v] = 0;
	}
	return currentjust[v]==0;
}

/**
 * If the rule with head v can be justified, do that justification.
 * Otherwise, add all nonjustified body literals to the queue that have to be propagated (no negative body literals in a rule)
 *
 * @Post: v is now justified if a justification can be found based on the current seen vector
 * @Returns: true if v is now justified
 */
bool IDSolver::directlyJustifiable(Var v, std::set<Var>& ufs, Queue<Var>& q) {
	vec<Lit> jstf;
	vec<Var> nonjstf;
	bool justified;
	switch(defType[v]){
	case CONJ:
		justified = findJustificationConj(v, jstf, nonjstf, seen);
		break;
	case DISJ:
		justified = findJustificationDisj(v, jstf, nonjstf, seen);
		break;
	case AGGR:
		justified = findJustificationAggr(v, jstf, nonjstf, seen);
		break;
	default:
		assert(false);
		reportf("The program tried to justify an rule that was not AGGR, DISJ or CONJ.\n");
		exit(3);
	}
	if(justified){
		changejust(v, jstf);
	}else{
		for(int i=0; i<nonjstf.size(); i++){
			assert(!isJustified(nonjstf[i]));
			if (inSameSCC(nonjstf[i], v)){
				if(ufs.insert(nonjstf[i]).second){ //set insert returns true (in second) if the insertion worked (no duplicates)
					q.insert(nonjstf[i]);
				}
			}
		}
	}
	return isJustified(v);
}

/**
 * Propagate the fact that v has been justified.
 *
 * Returns true if cs is now justified (and no longer a cycle source)
 */
bool IDSolver::propagateJustified(Var v, Var cs, std::set<Var>& ufs) {
	vec<Var> justifiedq;
	justifiedq.push(v); // literals that have to be justified
	while (justifiedq.size() > 0) {
		Var k = justifiedq.last();
		justifiedq.pop();

		// Make it justified.
		ufs.erase(k);
		isCS[k] = false;

		if (k == cs){
			return true;
		}

		Lit bdl = createPositiveLiteral(k);

		vec<Lit> heads;
		vec<vec<Lit> > jstf;
		propagateJustificationDisj(bdl, jstf, heads);
		propagateJustificationConj(bdl, jstf, heads);
		propagateJustificationAggr(bdl, jstf, heads);

		for(int i=0; i<heads.size(); i++){
			changejust(var(heads[i]), jstf[i]);
			justifiedq.push(var(heads[i]));
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void IDSolver::changejust(Var v, vec<Lit>& j) {
	justification[v].clear();
	j.copyTo(justification[v]);
}

/**
 * Creates the loop formula given an unfounded set
 */
void IDSolver::addExternalDisjuncts(const std::set<Var>& ufs, vec<Lit>& loopf){
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		switch (getDefType(*tch)) {
		case CONJ:
			break;
		case DISJ:{
			Rule& c = *definition[*tch];
			for (int i = 0; i < c.size(); i++) {
				Lit l = c[i];
				//add literals not in the ufs and not the head as external disjuncts
				if (l != c.getHeadLiteral() && seen[var(l)] != (isPositive(l) ? 2 : 1) && ufs.find(var(c[i])) == ufs.end()) {
					loopf.push(l);
					//remembers whether a literal has already been added, but both P and ~P can be added ONCE
					seen[var(l)] = (isPositive(l) ? 2 : 1); // Just in case P and ~P both appear; otherwise we might get something between well-founded and ultimate semantics...
				}
			}
			break;
		}
		case AGGR:
			aggsolver->createLoopFormula(*tch, ufs, loopf, seen);
			break;
		default:
			assert(false);
			reportf("Only AGGR, CONJ or DISJ should be checked for external disjuncts!");
			exit(3);
			break;
		}
	}

	for (int i = 1; i < loopf.size(); i++){
		seen[var(loopf[i])]=0;
	}
}

/**
 * If an atom of 'ufs' was already true, return a loop formula for this (one such) atom as conflicting clause.
 * Otherwise, add a loop formula for each atom in ufs, enqueue the negation of
 * each of those atoms, and return NULL.
 * For each atom in UFS that is false, don't do anything
 *
 * Loop formulas are created in the form
 * UFSLITERAL IMPLIES DISJUNCTION(external disjuncts)
 *
 * @Return a conflict clause if any conflict is found
 */
Clause* IDSolver::assertUnfoundedSet(const std::set<Var>& ufs) {
	assert(!ufs.empty());

	// Create the loop formula: add the external disjuncts (first element will be filled in later).
	vec<Lit> loopf(1);
	addExternalDisjuncts(ufs, loopf);

	if (defn_strategy != always) {// Maybe the loop formula could have been derived at an earlier level: in that case we first have to backtrack to that level.
		// Set the backtrack level.
		int lvl = 0;
		for (int i = 1; i < loopf.size(); i++){
			int litlevel = solver->getLevel(var(loopf[i]));
			if (litlevel > lvl){
				lvl = litlevel;
			}
		}
		solver->backtrackTo(lvl);
	}

	// Check if any of the literals in the loop are already true, which leads to a conflict.
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		if (isTrue(*tch)) {
			loopf[0] = createNegativeLiteral(*tch);	//negate the head to create a clause
			Clause* c = Clause_new(loopf, true);
			if(c->size()>1){
				solver->addLearnedClause(c);
				if (verbosity >= 2) {
					reportf("Adding conflicting loop formula: [ ");	printClause(*c); reportf("].\n");
				}
			}else{
				if (verbosity >= 2) {
					reportf("Adding conflicting loop formula: [ ");	printLit((*c)[0]); reportf("].\n");
				}
			}
			return c;
		}
	}

	// No conflict: then enqueue all facts and their loop formulas.
	if (loopf.size() >= 5) {
		//introduce a new var to represent all external disjuncts: v <=> \bigvee external disj
        Var v = solver->newVar();
        if (verbosity >= 2) { reportf("Adding new variable for loop formulas: %d.\n",v+1); }

        // ~v \vee \bigvee\extdisj{L}
        addLoopfClause(createNegativeLiteral(v), loopf);

        // \forall d \in \extdisj{L}: ~d \vee v
        vec<Lit> binaryclause(2); binaryclause[1] = createPositiveLiteral(v);
        for (int i=1; i<loopf.size(); ++i) {
        	addLoopfClause(~loopf[i], binaryclause);
        }

        loopf.shrink(2);

        //the end loop formula just contains v
        loopf[1] = createPositiveLiteral(v);
	}

	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		if(isUnknown(*tch)){
			Clause* c = addLoopfClause(createNegativeLiteral(*tch), loopf);
			solver->setTrue(loopf[0], c);
		}
	}

    return NULL;
}

Clause* IDSolver::addLoopfClause(Lit l, vec<Lit>& lits){
	lits[0] = l;
	Clause* c = Clause_new(lits, true);
	if(c->size()>1){
		solver->addLearnedClause(c);
		if (verbosity >= 2) {reportf("Adding loop formula: [ "); printClause(*c); reportf("].\n");}
	}else{
		if (verbosity >= 2) {reportf("Adding loop formula: [ "); printLit((*c)[0]); reportf("].\n");}
	}

	return c;
}

/* Precondition:  seen[i]==0 for each i.
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

void IDSolver::markNonJustifiedAddParents(Var x, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
	Lit poslit = createPositiveLiteral(x);
	vec<Var>& v = disj_occurs[toInt(poslit)];
	for (int i = 0; i < v.size(); ++i){
		if (var(justification[v[i]][0]) == x){
			markNonJustifiedAddVar(v[i], cs, q, tmpseen);
		}
	}
	vec<Var>& w = conj_occurs[toInt(poslit)];
	for (int i = 0; i < w.size(); i++){
		markNonJustifiedAddVar(w[i], cs, q, tmpseen);
	}
	if (aggsolver!=NULL) {
		vec<Var> heads;
		aggsolver->getHeadsOfAggrInWhichOccurs(x, heads);
		for(int i=0; i<heads.size(); i++){
			vec<Lit>& jstfc = justification[heads[i]];
			for (int k=0; k < jstfc.size(); k++){
				if(jstfc[k] == poslit){ // Found that x is actually used in y's justification.
					markNonJustifiedAddVar(heads[i], cs, q, tmpseen);
					break;
				}
			}
		}
	}
}

inline void IDSolver::markNonJustifiedAddVar(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
	if (isJustified(v) && inSameSCC(v, cs) && (defn_search == include_cs || v == cs || !isCS[v])) {
		seen[v] = 1;
		tmpseen.push(v);
		q.insert(v);
	}
}

/**
 * Propagates the changes from supporting to cycle free
 */
inline void IDSolver::apply_changes() {
	if (defn_strategy == adaptive) {
		if (adaption_current == adaption_total) {
			adaption_total++; // Next time, skip one decision level extra.
		}else{
			adaption_total--;
		}
		if (adaption_total < 0){
			adaption_total = 0;
		}
		adaption_current = 0;
	}
}

/*********************
 * AGGSOLVER METHODS *
 *********************/

vec<Lit>& IDSolver::getCFJustificationAggr(Var v){
	return justification[v];
}

/**
 * Checks whether the aggregate head v has a new external justification (just).
 * If this is the case (all literal in other scc than v or not defined in pos graph), then the new just is added.
 * Otherwise, v is added as a cycle source.
 */
void IDSolver::cycleSourceAggr(Var v, vec<Lit>& just){
	bool alljustifiedexternally = true;
	for(int i=0; alljustifiedexternally && i<just.size(); i++){
		if(isDefInPosGraph(var(just[i])) && inSameSCC(v, var(just[i]))){
			alljustifiedexternally = false;
		}
	}
	if(!alljustifiedexternally){
		addCycleSource(v);
	}else{
		changejust(v, just);
	}
}

void IDSolver::notifyAggrHead(Var head){
	assert(!isDefined(head));
	defType[head] = AGGR;
	defOcc[head] = NONDEFOCC;
	defdVars.push(head);
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
 * For debugging purposes, checks for POSITIVE LOOPS.
 */
bool IDSolver::isCycleFree() {
    assert(aggsolver==NULL);

    if(verbosity>=2){
        reportf("Showing cf- and sp-justification for disjunctive atoms. <<<<<<<<<<\n");
        for (int i = 0; i < nVars(); i++) {
            if (getDefType(i)==DISJ) {
                printLit(Lit(i,false)); reportf(" <- ");
                printLit(justification[i][0]);
                reportf("(cf); ");
            }
        }
        reportf(">>>>>>>>>>\n");
    }

    // Verify cycles.
    vec<int> isfree; // per variable. 0 = free, >0 = number of literals in body still to be justified.
    isfree.growTo(nVars(), 0);
    vec<Lit> justified;
    int cnt_nonjustified = 0;
    for (int i=0;i<nVars();++i) {
        justified.push(Lit(i,true)); // negative literals are justified anyhow.
        if (!isDefInPosGraph(i)) {
            justified.push(Lit(i,false));
        } else {
            ++cnt_nonjustified;
            isfree[i]=getDefType(i)==CONJ ? definition[i]->size() : 1;
        }
    }

    if(cnt_nonjustified==0){
    	return true;
    }

    int idx=0;
    while (cnt_nonjustified>0 && idx<justified.size()) {
        Lit l = justified[idx++];

        // Occurrences as justifying literal.
        vec<Var>& ds = disj_occurs[toInt(l)];
        vec<Var>& cs = conj_occurs[toInt(l)];
        vec<Var> as;
        if(aggsolver!=NULL){
        	aggsolver->getHeadsOfAggrInWhichOccurs(var(l), as);
        }

        for (int i=0;i<ds.size();++i) {
            Var d = ds[i];
            if (justification[d][0]==l && isfree[d]>0) {
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
        for (int i=0;i<as.size();++i) {
            Var d = as[i];
            bool found = false;
            for(int j=0; j<justification[d].size(); j++){
            	if (justification[d][j]==l && isfree[d]>0) {
            		found = true;
            		break;
            	}
            }
            if(found){
            	isfree[d]--;
            }
            if (isfree[d]==0) {
                justified.push(Lit(d,false));
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
                        reportf("D %d justified by ",v+1); printLit(justification[v][0]); reportf(".\n");
                        if (!printed[var(justification[v][0])]){
                        	cycle.push(var(justification[v][0]));
                        }
                    } else if(getDefType(v)==CONJ){
                        reportf("C %d has",v+1);
                        Rule& c = *definition[v];
                        for (int j=0; j<c.size(); j++) {
                            Var vj = var(c[j]);
                            if (c[j]!=c.getHeadLiteral() && isPositive(c[j]) && (isfree[vj]!=0 || printed[vj])) {
                                reportf(" %d",vj+1);
                                if (!printed[vj]){
                                	cycle.push(vj);
                                }
                            }
                        }
                        reportf(" in its body.\n");
                    }else{
                    	reportf("Change aggregate output here (iscyclefree method)"); //TODO change output (and make the method used by the solver
                    }
                    printed[v]=true;
                }
                for (int j=0;j<cycle.size();j++){
                	isfree[cycle[j]]=0;
                }
            }
        }
    } else
        reportf("OK; justification is cycle free.\n");
    return cnt_nonjustified==0;
}

/****************************
 * WELL FOUNDED MODEL CHECK *
 ****************************/

/**
 * ALGORITHM
 * The point is to calculate both an underapproximation and an overapproximation regarding the negative defined body literals, by
 * using for each iterating the derivation of the rule heads until the least fixpoint.
 * This boils down to two steps: in the first step, assuming all positive and all negative defined body literals are false and starting
 * derivation from there. Each time a head can be derived (in the underderivation, so certainly true), its body occurences can be updated.
 * When fixpoint is reached, then all negative defined body literals are made true (unless already derived), and in the same way an over
 * approximation is calculated (the positive body literals are still false). Everything that is derived there can still become true. So
 * all heads that are not derived after step two are certainly false. These steps are then iterated until complete fixpoint.
 * Optimisation 1: mark all literals that still have to be derived, avoiding to rederive them each iteration.
 * Optimisation 2: use counters indicating how many more elements have to become defined to be able to derive the head.
 *
 * Everything that is not derived in the end is unknown in the three-valued well-founded model, meaning that there is no two-valued well-
 * founded model, so the current interpretation is not a valid well-founded model.
 */
/**
 * FIXME currently no well founded model checking over aggregates
 * this can be done by implementing wf propagation and counter methods in aggregates.
 */
bool IDSolver::isWellFoundedModel() {
	if(!negloops){
		return true;
	}

	if(aggsolver!=NULL){
		reportf("For recursive aggregates, only stable semantics are currently supported!");
		return true;
	}

	// Initialize scc of full dependency graph
	wfroot.resize(nVars(), -1);
	vector<Var> rootofmixed;
	wfisMarked.resize(nVars(), false);
	//seen is used as justification counters, expected to be a vec of 0 of size nvars

	findMixedCycles(wfroot, rootofmixed);

	if(verbosity > 1){
		reportf("general SCCs found");
		for(vector<int>::size_type z=0; z<wfroot.size(); z++){
			reportf("%d has root %d\n", z, wfroot[z]);
		}
		reportf("Mixedcycles are %s present: \n", rootofmixed.empty()?"not":"possibly");
	}

	if(rootofmixed.empty()){
		return true;
	}

	markUpward();

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
	wffixpoint = false;
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

	for(int i=0; i<nVars(); i++){
		seen[i]=0;
	}

	return false;
}

/**
 * Visit the heads of all rules and check the current JUSTIFICATION graph for loops with mixed signs (because of standard propagation,
 * there are no other loops). The head is always positive, so pure negative loops are not possible.
 */
void IDSolver::findMixedCycles(vector<Var> &root, vector<int>& rootofmixed) {
	vector<bool> incomp(nVars(), false);
	stack<Var> stack;
	vector<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	int counter = 1;

	for(int i=0; i<defdVars.size(); i++){
		Var v = defdVars[i];
		if(visited[v]==0){
			visitWF(v, root, incomp, stack, visited, counter, true, rootofmixed);
		}
	}
}

void IDSolver::visitWF(Var v, vector<Var> &root, vector<bool> &incomp, stack<Var> &stack, vector<Var> &visited, int& counter, bool throughPositiveLit, vector<int>& rootofmixed) {
	assert(!incomp[v]);
	++counter;
	visited[v] = throughPositiveLit?counter:-counter;
	root[v] = v;
	stack.push(v);

	bool headtrue = value(v)==l_True;

	if(defType[v]==AGGR){
		/*vec<Lit> lits;
		aggsolver->getLiteralsOfAggr(v, lits);
		for(int i=0; i<lits.size(); i++){
			Lit l = lits[i];
			Var w = var(l);
			if(!isDefined(w)){
				continue;
			}
			if(visited[w]==0){
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			}else if(!incomp[w] && !isPositive(l) && visited[v]>0){
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]])>abs(visited[root[w]])){
				root[v] = root[w];
			}
		}*/
	}else if((headtrue && isConjunctive(v)) || (!headtrue && isDisjunctive(v))){
	//head is false and disj, or head is true and conj: all body literals are its justification
		for(int i=0; i<definition[v]->size(); i++){
			Lit l = definition[v]->operator [](i);
			Var w = var(l);
			if(!isDefined(w)){
				continue;
			}
			if(visited[w]==0){
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			}else if(!incomp[w] && !isPositive(l) && visited[v]>0){
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]])>abs(visited[root[w]])){
				root[v] = root[w];
			}
		}
	}else{//head is true and DISJ or head is false and CONJ: one literal is needed for justification
			// for DISJ, the justification is already known
			// for a CONJ, randomly choose one of the false body literals. If there is no loop through it, then it is a good choice.
			//			If there is, it will be found later if another false literal exists without a mixed loop.
		Lit l;
		if(isConjunctive(v)){
			for(int i=0; i<definition[v]->size(); i++){
				Lit l2 = definition[v]->operator [](i);
				if(isFalse(l2)){
					l=l2;
					break;
				}
			}
		}else{
			l = justification[v][0];
		}
		Var w = var(l);
		if(isDefined(w)){
			if(visited[w]==0){
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			}else if(!incomp[w] && !isPositive(l) && visited[v]>0){
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]])>abs(visited[root[w]])){
				root[v] = root[w];
			}
		}
	}

	if (root[v] == v) {
		wfrootnodes.push_back(v);
		bool mixed = false;
		int w;
		do {
			w = stack.top();
			stack.pop();
			visited[w]<0?mixed=true:true;
			root[w] = v; //these are the found sccs
			incomp[w] = true;
		} while (w != v);
		if(mixed){
			rootofmixed.push_back(v);
		}
	}
}

/**
 * De markering geeft aan welke atomen nog UNKNOWN zijn, dus in de huidige iteratie nog niet konden worden
 * afgeleid door de lower en upper bounds.
 *
 * Hoe de initiele bepalen: de cycle source is unknown. Alle heads die daarvan afhangen omdat het in de justification zit zijn unknown
 *
 * Dus vanaf nu markering voor VARS niet voor literals
 */

/**
 * Marks the head of a rule
 */
void IDSolver::mark(Var h) {
	Lit l = Lit(h, isFalse(h));	//holds the literal that has to be propagated, so has the model value
	if(!wfisMarked[h]){
		wfqueue.push(l);
		wfisMarked[h] = true;
		wfmarkedAtoms.insert(h);
	}
}

/**
 * marks all literals that can be reached upwards from the cycle roots.
 */
void IDSolver::markUpward() {
	for(vector<Var>::size_type n = 0; n < wfrootnodes.size(); ++n) {
		Var temp = wfrootnodes[n];
		mark(temp);
	}

	while(!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			mark(head);
		}
		for(int i=0; i<conj_occurs[toInt(~l)].size(); i++){
			Var head = conj_occurs[toInt(~l)][i];
			mark(head);
		}

		//false DISJ with -l in body, true DISJ with l as just
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			if((isTrue(head) && justification[head][0]==l) || isFalse(head)){
				mark(head);
			}
		}
		for(int i=0; i<disj_occurs[toInt(~l)].size(); i++){
			Var head = disj_occurs[toInt(~l)][i];
			if((isTrue(head) && justification[head][0]==~l) || isFalse(head)){
				mark(head);
			}
		}

		/*if(aggsolver!=NULL){
			vec<Lit> heads;
			aggsolver->getHeadsOfAggrInWhichOccurs(var(l), heads);
			for(int i=0; i<heads.size(); i++){
				mark(heads[i]);
			}
		}*/
	}
}

/**
 * Initializes the body counter of the rules on the number of marked body literals.
 * If there are no unmarked literals (counter==0) or the value can be derived directly from only one atom (disj and true, conj and false)
 * the head is pushed on the propagation q.
 *
 * The CONJ counters count the number of literals still needed to make the CONJ true
 * The DISJ counters count the number of literals still needed to make the DISJ false
 */
void IDSolver::initializeCounters() {
	for(set<Var>::iterator i=wfmarkedAtoms.begin(); i!=wfmarkedAtoms.end(); i++){
		Var v = *i;
		seen[v] = 0;
		bool canbepropagated = false;
		for(int j=0; !canbepropagated && j<definition[v]->size(); j++){
			Lit bl = definition[v]->operator [](j);
			if(wfisMarked[var(bl)]){
				seen[v]++;
			}else if(isFalse(bl) && defType[v]==CONJ){
				canbepropagated = true;
			}else if(isTrue(bl) && defType[v]==DISJ && var(bl)!=v){
				canbepropagated = true;
			}
		}
		if(seen[v]==0 || canbepropagated){
			seen[v] = 0;
			wfqueue.push(isTrue(v)?createPositiveLiteral(v):createNegativeLiteral(v));
		}
	}
}

/*
 * marked geeft aan dat een atoom in de huidige iteratie nog unknown is. En de counter geven aan hoeveel er 
 * nog nodig zijn om de head respectievelijk true (conj) of false (disj) te maken
 * Maar de rest moet nog omgeschreven worden in deze vorm.
 *
 * De propagate queue is dan een queue die bijhoudt of iets een waarde heeft gekregen (de waarde van het model dan) en dat dat gepropageerd
 * moet worden
 */


/**
 * Counters probably keep the number of literals needed to make it true for CONJ and the number of literals needed to make it false for DISJ!!!
 */
void IDSolver::forwardPropagate(bool removemarks) {
	while(!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		if(!wfisMarked[var(l)]){
			continue;
		}
		wfisMarked[var(l)] = false;

		if(removemarks) {
			wfmarkedAtoms.erase(var(l));
			wffixpoint = false;
		}

		//Literal l has become true, so for all rules with body literal l and marked head,
		//if DISJ, then head will be true, so add true head to queue and set counter to 0
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			if(wfisMarked[head]) {
				wfqueue.push(createPositiveLiteral(head));
				seen[head] = 0;
			}
		}

		//if CONJ and counter gets 0, then head will be true, so add true head to queue
		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			if(wfisMarked[head] && --seen[head]==0){
				wfqueue.push(createPositiveLiteral(head));
			}
		}


		l = ~l;

		//Literal l has become false, so for all rules with body literal l and marked head,
		//if DISJ and counter gets 0, then head will be false, so add false head to queue
		for(int i=0; i<disj_occurs[toInt(l)].size(); i++){
			Var head = disj_occurs[toInt(l)][i];
			if(wfisMarked[head] && --seen[head]==0){
				wfqueue.push(createNegativeLiteral(head));
			}
		}

		//if CONJ, then head will be false, so add false head to queue and set counter to 0
		for(int i=0; i<conj_occurs[toInt(l)].size(); i++){
			Var head = conj_occurs[toInt(l)][i];
			if(wfisMarked[head]) {
				wfqueue.push(createNegativeLiteral(head));
				seen[head] = 0;
			}
		}

		//FIXME AGGREGATES
	}
}

/**
 * Overestimate the counters by making all negative defined marked body literals true.
 */
void IDSolver::overestimateCounters() {
	for(set<Var>::iterator i=wfmarkedAtoms.begin(); i!=wfmarkedAtoms.end(); i++){
		Var v = *i;
		assert(seen[v] > 0);

		for(int j=0; j<definition[v]->size(); j++){
			Lit bdl = definition[v]->operator [](j);
			if(wfisMarked[var(bdl)] && !isPositive(bdl) && v!=var(bdl)){
				if(defType[v]==CONJ){
					seen[v]--;
				}else{
					seen[v]=0;
				}
			}
		}

		if(seen[v]==0){
			wfqueue.push(createPositiveLiteral(v));
		}
	}
}


/**
 * Removes all elements from the marked stack that are still marked. These have not been derived, so are certainly false.
 * All those that are still on the marked stack, but are not longer marked, are still undefined after this iteration, so
 * are marked again.
 */
void IDSolver::removeMarks() {
	stack<Var> temp;
	for(set<Var>::iterator i=wfmarkedAtoms.begin(); i!=wfmarkedAtoms.end(); i++){
		Var v = *i;
		if(wfisMarked[v]) {
			temp.push(v);
			wfisMarked[v] = false;
			wffixpoint = false;
		}else {
			wfisMarked[v] = true;
		}
	}
	while(!temp.empty()) {
		wfmarkedAtoms.erase(temp.top());
		temp.pop();
	}
}

/***********************************************
 * TARJAN ALGORITHM FOR FINDING UNFOUNDED SETS *
 ***********************************************/

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
void IDSolver::changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<int>& vis){
	vec<Lit> queue;

	if(!hasJustificationTarjan(definednode, vis)){
		vec<Lit> j; j.push(firstjustification);
		changejust(definednode, j);
		vis[definednode]=-vis[definednode]; //set it as justified
		queue.push(Lit(definednode));
	}

	while(queue.size()>0){
		Lit just = queue.last();
		queue.pop();
		for(int i=0; i<network[visitedAtTarjan(var(just), vis)].size(); i++){
			Lit t = network[visitedAtTarjan(var(just), vis)][i];
			if(!hasJustificationTarjan(var(t), vis)){
				vec<Lit> j; j.push(just);
				changejust(var(t), j);
				vis[var(t)]=-vis[var(t)];
				queue.push(t);
			}
		}
	}
}

inline bool IDSolver::visitedEarlierTarjan(Var x, Var y, vec<Var>& vis){
	int x1 = vis[x]>0?vis[x]:-vis[x];
	int y1 = vis[y]>0?vis[y]:-vis[y];
	return x1<y1;
}

inline bool IDSolver::visitedTarjan(Var x, vec<Var>& vis){
	return vis[x]!=0;
}

inline int IDSolver::visitedAtTarjan(Var x, vec<Var>& vis){
	return vis[x]>0?vis[x]:-vis[x];
}

inline bool IDSolver::hasJustificationTarjan(Var x, vec<Var>& vis){
	return vis[x]<0;
}

/////////////
//Finding unfounded checks by
//validjust indicates both that the element is already in a justification or is in another found component (in which case it might also be false, not requiring a justification)
//TODO werkt niet voor aggregaten
UFS IDSolver::visitForUFSsimple(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& vis, vec<vec<Lit> >& network){
	vis[v]=visittime;
	int timevisited = visittime;
	visittime++;

	DefType type = getDefType(v);

	if(type==AGGR){return OLDCHECK;}
	assert(type==CONJ || type==DISJ);

	Rule* c = definition[v];
	if(verbosity >=1){
		printClause(*c);
	}

	Lit definedChild;
	bool childfound = false;

	for(int i=0; i<c->size(); i++){
		DefType childtype = getDefType(var(c->operator [](i)));
		Lit l = c->operator [](i);
		if(var(l)==v){ continue; } //rule head or identical body atom
		if(childtype==AGGR){return OLDCHECK;}
		if(!isDefInPosGraph(var(c->operator [](i))) || !inSameSCC(var(l), v) || hasJustificationTarjan(var(l), vis)){
			if(!isFalse(l) && type==DISJ){
				changeJustificationsTarjan(v, l, network, vis);
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
			if(visitedTarjan(var(definedChild), vis)){
				network.growTo(visittime+1);
				network[visittime].push(Lit(v));
			}else{
				network[visitedAtTarjan(var(definedChild), vis)].push(Lit(v));
			}

			if(!visitedTarjan(var(definedChild), vis)){
				UFS ret = visitForUFSsimple(var(definedChild), ufs, visittime, stack, vis, network);
				if(ret != STILLPOSSIBLE){
					return ret;
				}
			}
			if(!hasJustificationTarjan(var(definedChild), vis) && visitedEarlierTarjan(var(definedChild), v, vis)){
				vis[v]=vis[var(definedChild)];
			}
		}
	}else{ //DISJ, have returned from all others
		for(int i=0; i<c->size(); i++){
			Var child = var(c->operator [](i));
			if(child==v){ continue;	}
			if(!(getDefType(child)==CONJ || getDefType(child)==DISJ)){continue;}

			if(!visitedTarjan(child, vis)){
				network.growTo(visittime+1);
				network[visittime].push(Lit(v));
			}else{
				network[visitedAtTarjan(child, vis)].push(Lit(v));
			}

			if(!visitedTarjan(child, vis)){
				UFS ret = visitForUFSsimple(child, ufs, visittime, stack, vis, network);
				if(ret!=STILLPOSSIBLE){
					return ret;
				}
			}
			if(!hasJustificationTarjan(child, vis) && visitedEarlierTarjan(child, v, vis)){
				vis[v]=vis[child];
			}
		}
	}

	if(visitedAtTarjan(v, vis)==timevisited){
		bool allfalse = true;
		Var x;
		do{
			x=stack.last();
			stack.pop();
			vis[x]=vis[x]>0?vis[x]:-vis[x];
			ufs.insert(x);
			if(!isFalse(x)){allfalse = false;}
		}while(x!=v);
		if(allfalse){
			ufs.clear();
			return STILLPOSSIBLE;
		}
		if(ufs.size()>1){
			if(verbosity >=4){
				fprintf(stderr, "ufsfound: ");
				for(std::set<Var>::iterator i=ufs.begin(); i!=ufs.end(); i++){
					Var x = *i;
					fprintf(stderr, "%d:%c", x << 1, isTrue(x) ? '1' : (isFalse(x) ? '0' : 'X'));
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
				if(verbosity >=4){
					fprintf(stderr, "ufsfound: ");
					for(std::set<Var>::iterator i=ufs.begin(); i!=ufs.end(); i++){
						Var x = *i;
						fprintf(stderr, "%d:%c", x << 1, isTrue(x) ? '1' : (isFalse(x) ? '0' : 'X'));
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
