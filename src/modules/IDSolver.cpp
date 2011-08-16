/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/IDSolver.hpp"
#include "utils/Print.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "modules/SCCtoCNF.hpp"

#include <cmath>

#include "utils/IntTypes.h"

// FIXME an unwellfounded model does NOT mean that the definition is not wellfounded
// TODO only add one loopform at a time (save all lits, check next time first whether all are false, otherwise choose one more)

using namespace std;
using namespace MinisatID;

IDSolver::IDSolver(PCSolver* s, int definitionID):
		Propagator(s),
		definitionID(definitionID),
		//minvar(-1), maxvar(-1), nbvars(0),
		minvar(0), nbvars(0),
		sem(getPCSolver().modes().defsem),
		posrecagg(true), mixedrecagg(true),
		previoustrailatsimp(-1),
		posloops(true), negloops(true),
		backtracked(true),
		adaption_total(0), adaption_current(0),
		atoms_in_pos_loops(0),
		cycle_sources(0), justifiable_cycle_sources(0), cycles(0), cycle_sizes(0), justify_conflicts(0),
		nb_times_findCS(0), justify_calls(0), cs_removed_in_justify(0), succesful_justify_calls(0),
		extdisj_sizes(0), total_marked_size(0)
		{
	getPCSolver().accept(this, EV_PRINTSTATS);
	getPCSolver().accept(this, EV_DECISIONLEVEL);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PRINTSTATE);
	getPCSolver().accept(this, EV_FULLASSIGNMENT);
	getPCSolver().acceptFinishParsing(this, true);
}

IDSolver::~IDSolver() {
	deleteList<DefinedVar> (definitions);
}

int	IDSolver::getNbOfFormulas() const {
	return definitions.size() * log(definitions.size());
}

inline void IDSolver::addCycleSource(Var v) {
	if (!isCS(v)) {
		isCS(v) = true;
		css.push_back(v);
	}
}
inline void IDSolver::clearCycleSources() {
	for (vv::const_iterator i = css.begin(); i < css.end(); ++i){
		isCS(*i) = false;
	}
	css.clear();
}

// TODO keep vector, make it a map, a queue? Parsing will go extremely slow if heads are in descending order for example
void IDSolver::adaptStructsToHead(Var head){
	/*	bool minchanged = false;
	bool maxchanged = false;
	if(minvar==-1 || head<minvar){
		minchanged = true;
	}
	if(maxvar==-1 || maxvar<head){
		maxvar = head;
		maxchanged = true;
	}
	if(minchanged){
		while(definitions.size()<maxvar-minvar+1){
			int size = definitions.size();
			definitions.insert(definitions.begin(), NULL);
			assert(size<definitions.size());
		}
		nbvars = definitions.size();
	}
	if(maxchanged){
		definitions.resize(maxvar-minvar+1, NULL);
		nbvars = definitions.size();
	}*/
	nbvars = nVars();
	definitions.resize(nbvars, NULL);
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
bool IDSolver::addRule(bool conj, Var head, const vec<Lit>& ps) {
	assert(!isInitialized());

	// LAZY init
	adaptStructsToHead(head);

	if(isDefined(head)){
		char s[100]; sprintf(s, "Multiple rules have the same head %d, which is not allowed!\n", getPrintableVar(head));
		throw idpexception(s);
	}

	bool notunsat = true;

	if (ps.size() == 0) {
		Lit h = conj ? mkLit(head) : mkLit(head, true); //empty set conj = true, empty set disj = false
		InnerDisjunction v;
		v.literals.push_back(h);
		notunsat = getPCSolver().add(v);
	} else {
		//rules with only one body atom have to be treated as conjunctive
		conj = conj || ps.size() == 1;

		PropRule* r = new PropRule(mkLit(head), ps);
		createDefinition(head, r, conj?CONJ:DISJ);

		InnerEquivalence eq;
		eq.head = mkLit(head);
		for(int i=0; i<ps.size(); ++i){
			eq.literals.push_back(ps[i]);
		}
		eq.conjunctive = conj;
		notunsat = getPCSolver().add(eq);
		assert(isDefined(head));
	}

	return notunsat;
}

void IDSolver::addDefinedAggregate(const InnerReifAggregate& inneragg, const InnerWLSet& innerset){
	Var head = inneragg.head;
	adaptStructsToHead(head);
	if(isDefined(head)){
		char s[100]; sprintf(s, "Multiple rules have the same head %d, which is not allowed!\n", getPrintableVar(head));
		throw idpexception(s);
	}

	AggBound b(inneragg.sign, inneragg.bound);
	IDAgg* agg = new IDAgg(mkLit(head), b, inneragg.sem, inneragg.type, innerset.wls);
	if(isInitiallyJustified(*agg)){
		delete(agg);
		return;
	}
	createDefinition(head, agg);
}

/*
 * Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
 *
 * @PRE: aggregates have to have been finished
 */
void IDSolver::finishParsing(bool& present, bool& unsat) {
	assert(isParsing());
	notifyParsed();
	present = true;
	unsat = false;

	if(modes().defsem==DEF_COMP || defdVars.size()==0){
		present = false;
		return;
	}

	//LAZY initialization
	_seen = new InterMediateDataStruct(nbvars, minvar);
	_disj_occurs.resize(nVars()*2, vector<Var>());
	_conj_occurs.resize(nVars()*2, vector<Var>());
	_aggr_occurs.resize(nVars()*2, vector<Var>());

	for (auto i=defdVars.begin(); i!=defdVars.end(); ++i) {
		occ(*i)=NONDEFOCC;
	}

#ifdef DEBUG
	for (auto i=defdVars.begin(); i!=defdVars.end(); ++i) {
		assert(isDefined(*i));
		assert(occ(*i)==NONDEFOCC);
	}
#endif

	if (verbosity() >= 1) {
		report("> Number of rules : %6zu.\n",defdVars.size());
	}

	// A heuristic might be constructed which bump when head vars are assigned e.g.

	// Initialize scc of full dependency graph
	//TODO remove nVars!
	vec<bool> incomp(nVars(), false);
	vec<Var> stack;
	vec<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	vector<Var> sccroots, mixedroots;
	vec<Var> nodeinmixed;
	int counter = 1;

	for (vector<Var>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
		if (visited[(*i)] == 0) {
			visitFull((*i), incomp, stack, visited, counter, true, sccroots, mixedroots, nodeinmixed);
		}
	}

	int mixedsccs = mixedroots.size();

	//all var in rootofmixed are the roots of mixed loops. All other are no loops (size 1) or positive loops

	// Initialize scc of positive dependency graph
	for (int i = 0; i < nodeinmixed.size(); ++i) {
		incomp[nodeinmixed[i]] = false;
		occ(nodeinmixed[i]) = MIXEDLOOP;
		visited[nodeinmixed[i]] = 0;
	}
	stack.clear();
	counter = 1;

	for (int i = 0; i < nodeinmixed.size(); ++i) {
		if (visited[nodeinmixed[i]] == 0) {
			visit(nodeinmixed[i], incomp, stack, visited, counter, sccroots);
		}
	}

	if (verbosity() > 20) {
		report("Printing mapping from variables to the ID of the SCC in which it occurs:\n");
		for (vv::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
			report("SCC of %d is %d, ", getPrintableVar(*i), getPrintableVar(scc(*i)));
		}
		report("Ended printing sccs.\n");
	}

	// Determine which literals should no longer be considered defined (according to the scc in the positive graph) + init occurs
	atoms_in_pos_loops = 0;

	Lit l;
	vector<Var> reducedVars;
	mixedrecagg = false;
	posrecagg = false;
	for (auto i = defdVars.begin(); i < defdVars.end(); ++i) {
		Var v = (*i);
		bool isdefd = false;
		DefType t = type(v);
		switch (t) {
			case DISJ:
			case CONJ:
				for (vl::const_iterator j = definition(v)->begin(); j < definition(v)->end(); ++j) {
					l = *j;
					if (isPositive(l) && inSameSCC(v, var(l))) {
						isdefd = true;
					}
				}
				break;
			case AGGR: {
				for (vwl::const_iterator j = getSetLitsOfAggWithHeadBegin(v); !isdefd && j< getSetLitsOfAggWithHeadEnd(v); ++j) {
					if (inSameSCC(v, var((*j).getLit()))) { // NOTE: disregard sign here: set literals can occur both pos and neg in justifications.
						isdefd = true;
					}
				}
				break;
			}
		}

		bool addtonetwork = false;
		if (isdefd) { //might be in pos loop
			++atoms_in_pos_loops;
			occ(v) = occ(v) == MIXEDLOOP ? BOTHLOOP : POSLOOP;
			addtonetwork = true;
		} else { //can never be in posloop
			if (occ(v) == NONDEFOCC) { //will not occur in a loop
				removeDefinition(v);
			} else if (occ(v) == MIXEDLOOP) { //might occur in a mixed loop
				addtonetwork = true;
			}
		}

		if(addtonetwork){
			reducedVars.push_back(v);

			//IMPORTANT: also add mixed loop rules to the network for checking well-founded model
			//could be moved to different datastructure to speed up
			switch(t){
			case DISJ:
				for (auto j = definition(v)->begin(); j < definition(v)->end(); ++j) {
					l = *j;
					if(l==definition(v)->getHead()){
						continue;
					}
					addDisjOccurs(l, v);
				}
				break;
			case CONJ:
				for (auto j = definition(v)->begin(); j < definition(v)->end(); ++j) {
					l = *j;
					if(l==definition(v)->getHead()){
						continue;
					}
					addConjOccurs(l, v);
				}
				break;
			case AGGR:
				for (auto j=(*aggdefinition(v)).getWL().begin(); j!=(*aggdefinition(v)).getWL().end(); ++j) {
					addAggrOccurs((*j).getLit(), v);
				}
				switch(occ(v)){
				case MIXEDLOOP:
					mixedrecagg = true;
					break;
				case POSLOOP:
					posrecagg = true;
					break;
				case BOTHLOOP:
					mixedrecagg = true;
					posrecagg = true;
					break;
				default:
					break;
				}
				break;
			}
		}
	}
	defdVars.clear();
	defdVars.insert(defdVars.begin(), reducedVars.begin(), reducedVars.end());

	if (atoms_in_pos_loops == 0) {
		posloops = false;
	}
	if (mixedsccs == 0) {
		negloops = false;
	}

	if(getSemantics()==DEF_STABLE){
		negloops = false;
	}

	if (verbosity() >= 1) {
		report("> Number of recursive atoms in positive loops : %6d.\n",(int)atoms_in_pos_loops);
		if (negloops) {
			report("> Mixed loops also exist.\n");
		}
	}

	if (!posloops && !negloops) {
		present = false;
		return;
	}

	//This heuristic on its own solves hamiltonian path for slow decay
	if(modes().bumpidonstart){
		for (vector<Var>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
			const Var& v = *i;
			if(isDefined(v) && type(v)==DISJ){
				const PropRule& r = *definition(v);
				for(int j=0; j<r.size(); ++j){
					getPCSolver().varBumpActivity(var(r[j]));
				}
			}
		}
	}

	unsat = !simplifyGraph();

	// TODO in fact, having a propagator per scc might seem more logical?

	if(!unsat && modes().tocnf){
		vector<toCNF::Rule*> rules;
		for(auto root = sccroots.begin(); root!=sccroots.end(); ++root){
			// FIXME use current interpretation to decide which rules/sccs not to transform
			// TODO better to store full sccs instead having to loop over them here?
			for(auto i=defdVars.begin(); i<defdVars.end(); ++i){
				if(scc(*root)==scc(*i)){
					vector<Var> defbodylits;
					vector<Lit> openbodylits;
					auto proprule = getDefVar(*i)->definition();
					for(auto bodylit=proprule->begin(); bodylit!=proprule->end(); ++bodylit){
						if(not sign(*bodylit) && hasDefVar(var(*bodylit)) && scc(var(*bodylit))==scc(*root)){
							defbodylits.push_back(var(*bodylit));
						}else{
							openbodylits.push_back(*bodylit);
						}
					}
					toCNF::Rule* rule = new toCNF::Rule(isDisjunctive(*i), *i, defbodylits, openbodylits);
					rules.push_back(rule);
				}
			}
			unsat = not toCNF::transformSCCtoCNF(getPCSolver(), rules);
			deleteList<toCNF::Rule>(rules);
		}
		present = false;
		// TODO should still allow wellfoundedness checks here!
	}

	notifyInitialized();
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the FULL dependency graph
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visitFull(Var i, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited,
		int& counter, bool throughPositiveLit, vector<Var>& posroots, vector<Var>& rootofmixed, vec<Var>& nodeinmixed) {
	assert(!incomp[i]);
	assert(isDefined(i));
	++counter;
	visited[i] = throughPositiveLit ? counter : -counter;
	scc(i) = i;
	stack.push(i);

	switch (type(i)) {
		case DISJ:
		case CONJ: {
			PropRule const * const r = definition(i);
			for (int j = 0; j < r->size(); ++j) {
				Lit l = (*r)[j];
				int w = var(l);
				if (!isDefined(w)) {
					continue;
				}

				if (visited[w] == 0) {
					visitFull(w, incomp, stack, visited, counter, isPositive(l), posroots, rootofmixed, nodeinmixed);
				} else if (!incomp[w] && !isPositive(l) && visited[i] > 0) {
					visited[i] = -visited[i];
				}
				if (!incomp[w] && abs(visited[scc(i)]) > abs(visited[scc(w)])) {
					scc(i) = scc(w);
				}
			}
			break;
		}
		case AGGR: {
			for (vwl::const_iterator j = getSetLitsOfAggWithHeadBegin(i); j<getSetLitsOfAggWithHeadEnd(i); ++j) {
				Var w = var((*j).getLit());
				if (!isDefined(w)) {
					continue;
				}

				if (visited[w] == 0) {
					visitFull(w, incomp, stack, visited, counter, false /*Over-approximation of negative occurences*/, posroots, rootofmixed, nodeinmixed);
				} else if (!incomp[w] && visited[i] > 0) { // Over-approximation of negative occurences
					visited[i] = -visited[i];
				}
				if (!incomp[w] && abs(visited[scc(i)]) > abs(visited[scc(w)])) {
					scc(i) = scc(w);
				}
			}
			break;
		}
	}

	if (scc(i) == i) {
		vec<Var> sccs;
		bool mixed = false;
		int w;
		posroots.push_back(i);
		do {
			w = stack.last();
			stack.pop();
			visited[w] < 0 ? mixed = true : true;
			scc(w) = i; //these are the found sccs
			sccs.push(w);
			incomp[w] = true;
		} while (w != i);
		if (mixed && sccs.size()>1) {
			rootofmixed.push_back(i);
			for (int i = 0; i < sccs.size(); ++i) {
				nodeinmixed.push(sccs[i]);
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
void IDSolver::visit(Var i, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited, int& counter, vector<Var>& roots) {
	assert(scc(i)>=0 && scc(i)<nbvars);
	assert(!incomp[i]);
	visited[i] = ++counter;
	scc(i) = i;
	stack.push(i);

	switch (type(i)) {
		case DISJ:
		case CONJ: {
			PropRule const * const r = definition(i);
			for (int j = 0; j < r->size(); ++j) {
				Lit l = (*r)[j];
				Var w = var(l);
				if (isDefined(w) && i != w && isPositive(l)) {
					if (visited[w] == 0) {
						visit(w, incomp, stack, visited, counter, roots);
					}
					if (!incomp[w] && visited[scc(i)] > visited[scc(w)]) {
						scc(i) = scc(w);
					}
				}
			}
			break;
		}
		case AGGR: {
			//TODO this can be optimized by using another method which only returns literals possibly in the positive dependency graph.
			for (vwl::const_iterator j = getSetLitsOfAggWithHeadBegin(i); j<getSetLitsOfAggWithHeadEnd(i); ++j) {
				Var w = var((*j).getLit());
				if (!isDefined(w)) {
					continue;
				}

				if (visited[w] == 0) {
					visit(w, incomp, stack, visited, counter, roots);
				}
				if (!incomp[w] && visited[scc(i)] > visited[scc(w)]) {
					scc(i) = scc(w);
				}
			}
			break;
		}
		default:
			assert(false);
	}

	if (scc(i) == i) {
		int w;
		roots.push_back(i);
		do {
			w = stack.last();
			stack.pop();
			scc(w) = i; //these are the found sccs
			incomp[w] = true;
		} while (w != i);
	}
}

bool IDSolver::simplifyGraph(){
	if(!posloops){
		return true;
	}

	//The next is a check on when to do the simplification again
	assert(getPCSolver().getDecisions().size()==0);
	int currenttrailsize = getPCSolver().getTrail().size();
	if (currenttrailsize == previoustrailatsimp) {
		return true;
	} else { //Not same base assertions, so simplify again
		assert(currenttrailsize>previoustrailatsimp);
		previoustrailatsimp = currenttrailsize;
	}

	for(vv::const_iterator i=defdVars.begin(); i<defdVars.end(); ++i){
		justification(*i).clear();
	}

	vector<Var> usedseen; //stores which elements in the "seen" datastructure we adapted to reset them later on
	for (vv::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
		Var v = (*i);
		if (isFalse(v)) {
			continue;
		}
		switch (type(v)) {
			case DISJ:
			case AGGR:
				seen(v) = 1;
				break;
			case CONJ:
				seen(v) = definition(v)->size();
				break;
			default:
				assert(false);
		}
		usedseen.push_back(v);
	}

	// initialize a queue of literals that are safe with regard to cycle-freeness. (i.e.: either are not in justification, or are justified in a cycle-free way.)
	queue<Lit> propq;
	for (int i = 0; i < nVars(); ++i) {
		Lit l = createNegativeLiteral(i);
		if (!isFalse(l)) {
			propq.push(l); // First negative literals are added that are not already false
		}
		l = createPositiveLiteral(i);
		if (!isDefInPosGraph(i) && !isFalse(l)) {
			if(isDefined(var(l))){
				seen(var(l)) = 0; //Mixed loop is justified, so seen is 0 (otherwise might find the same literal multiple times)
			}
			propq.push(l); // Then all non-false non-defined positive literals.
		}
	}

	// propagate safeness to defined literals until fixpoint.
	// While we do this, we build the initial justification.
	while (!propq.empty()) {
		Lit l = propq.front(); //only heads are added to the queue
		assert(sign(l) || !isDefined(var(l)) || (seen(var(l))==0));
		propq.pop();

		vec<Lit> heads;
		vec<vec<Lit> > jstf;

		propagateJustificationDisj(l, jstf, heads);
		for (int i = 0; i < heads.size(); ++i) {
			assert(jstf[i].size()>0);
			changejust(var(heads[i]), jstf[i]);
			propq.push(heads[i]);
		}
		heads.clear();
		jstf.clear();

		propagateJustificationAggr(l, jstf, heads);
		for (int i = 0; i < heads.size(); ++i) {
			changejust(var(heads[i]), jstf[i]);
			propq.push(heads[i]);
		}
		heads.clear();
		jstf.clear();

		propagateJustificationConj(l, propq);
	}

	if (verbosity() >= 2) {
		report("Initialization of justification makes these atoms false: [");
	}

	/**
	 * Goes through all definitions and checks whether they can still become true (if they have been
	 * justified). Otherwise, it is checked (overestimation) whether a negative loop might be possible.
	 * If this is not the case, the definition is removed from the data structures.
	 */
	vector<Var> reducedVars;
	posrecagg = false;
	mixedrecagg = false;
	for (vector<int>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
		Var v = (*i);
		if (seen(v) > 0 || isFalse(v)) {
			if (verbosity() >= 2) {
				report(" %d", getPrintableVar(v));
			}
			if (isTrue(v)) {
				return false;
			} else if (isUnknown(v)) {
				getPCSolver().setTrue(createNegativeLiteral(v), this);
			}

			if (occ(v) == POSLOOP) {
				removeDefinition(v);
				--atoms_in_pos_loops;
			} else {
				occ(v) = MIXEDLOOP;
				reducedVars.push_back(v);
				if (type(v) == AGGR) {
					mixedrecagg = true;
				}
			}
		} else {
			reducedVars.push_back(v);
			if(type(v)==AGGR){
				switch(occ(v)){
				case MIXEDLOOP:
					mixedrecagg = true;
					break;
				case POSLOOP:
					posrecagg = true;
					break;
				case BOTHLOOP:
					mixedrecagg = true;
					posrecagg = true;
					break;
				default:
					break;
				}
			}
		}
	}
	defdVars.clear();
	defdVars.insert(defdVars.begin(), reducedVars.begin(), reducedVars.end());

	//reconstruct the disj and conj occurs with the reduced number of definitions
	_disj_occurs.clear();
	_conj_occurs.clear();
	_disj_occurs.resize(2*nVars(), vector<Var>());
	_conj_occurs.resize(2*nVars(), vector<Var>());
	for (vector<int>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
		Var v = (*i);
		if (type(v) == CONJ || type(v) == DISJ) {
			const PropRule& dfn = *definition(v);
			for (int j = 0; j < dfn.size(); ++j) {
				Lit l = dfn[j];
				if (l != dfn.getHead()) { //don't look for a justification that is the head literal itself
					if (type(v) == DISJ) {
						addDisjOccurs(l, v);
					} else if (type(v) == CONJ) {
						addConjOccurs(l, v);
					}
				}
			}
		}else{
			const IDAgg& dfn = *aggdefinition(v);
			for (auto j=dfn.getWL().begin(); j!=dfn.getWL().end(); ++j) {
				addAggrOccurs((*j).getLit(), v);
			}
		}
	}

	//Reset the elements in "seen" that were changed
	//IMPORTANT do not return before this call!
	for (vv::const_iterator i = usedseen.begin(); i < usedseen.end(); ++i) {
		seen(*i) = 0;
	}

	if (verbosity() >= 2) {
		report(" ]\n");
	}

	if (atoms_in_pos_loops == 0) {
		posloops = false;
	}

	if (!posloops && !negloops) {
		if (verbosity() >= 1) {
			report("> All recursive atoms falsified in initializations.\n");
		}
	}

	if(posloops && modes().defn_strategy != adaptive && !isCycleFree()) {
		throw idpexception("Positive justification graph is not cycle free!\n");
	}
#ifdef DEBUG
	if(verbosity()>=9){
		clog <<"Justifications:\n";
	}
	int count = 0;
	for (vv::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
		Var var = *i;
		assert(hasDefVar(var));
		assert(justification(var).size()>0 || type(var)!=DISJ || occ(var)==MIXEDLOOP);

		if(verbosity()>=9){
			clog <<getPrintableVar(var) <<"<-";
			bool begin = true;
			count++;
			for(int i=0; i<justification(var).size(); i++){
				if(!begin){
					clog <<",";
				}
				begin = false;
				clog <<justification(var)[i];
			}
			clog <<";";
			if(count%30==0){
				clog <<"\n";
			}
		}

		Lit l(createPositiveLiteral(var));
		if(hasdisj_occurs(l)){
			for (vector<Var>::const_iterator j = disj_occurs(l).begin(); j < disj_occurs(l).end(); ++j) {
				assert(type(*j)==DISJ);
			}
		}
		if(hasconj_occurs(l)){
			for (vector<Var>::const_iterator j = conj_occurs(l).begin(); j < conj_occurs(l).end(); ++j) {
				assert(type(*j)==CONJ);
			}
		}
		l = createNegativeLiteral(var);
		if(hasdisj_occurs(l)){
			for (vector<Var>::const_iterator j = disj_occurs(l).begin(); j < disj_occurs(l).end(); ++j) {
				assert(type(*j)==DISJ);
			}
		}
		if(hasconj_occurs(l)){
			for (vector<Var>::const_iterator j = conj_occurs(l).begin(); j < conj_occurs(l).end(); ++j) {
				assert(type(*j)==CONJ);
			}
		}
	}
	if(verbosity()>=9){
		clog <<"\n";
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
void IDSolver::propagateJustificationDisj(const Lit& l, vec<vec<Lit> >& jstf, vec<Lit>& heads) {
	if(hasdisj_occurs(l)){
		const vector<Var>& disj = disj_occurs(l);
		for (vector<Var>::const_iterator i = disj.begin(); i < disj.end(); ++i) {
			const Var& v = *i;
			if (isFalse(v) || seen(v) == 0) {
				continue;
			}
			seen(v) = 0;
			heads.push(createPositiveLiteral(v));
			jstf.push();
			jstf.last().push(l);
		}
	}
}

template<typename T>
void IDSolver::propagateJustificationConj(const Lit& l, T& heads) {
	if(hasconj_occurs(l)){
		const vector<Var>& ll = conj_occurs(l);
		for (vector<Var>::const_iterator i = ll.begin(); i < ll.end(); ++i) {
			const Var& v = *i;
			if (isFalse(v) || seen(v) == 0) {
				continue;
			}
			seen(v)--;
			if (seen(v) == 0) {
				heads.push(createPositiveLiteral(v));
			}
		}
	}
}

void IDSolver::propagateJustificationAggr(const Lit& l, vec<vec<Lit> >& jstfs, vec<Lit>& heads) {
	for(vector<Var>::const_iterator i = aggr_occurs(l).begin(); i < aggr_occurs(l).end(); ++i) {
		const IDAgg& agg = *aggdefinition(*i);
		if (isFalse(agg.getHead())) {
			continue;
		}

		Var head = var(agg.getHead());
		if (seen(head) > 0) { //only check its body for justification when it has not yet been derived
			vec<Lit> jstf;
			vec<Var> nonjstf;

			if (canJustifyHead(agg, jstf, nonjstf, *_seen, false)) {
				seen(head) = 0;
				heads.push(mkLit(head, false));
				jstfs.push();
				jstf.copyTo(jstfs.last());
			}
		}
	}
}

/*
 * IMPORTANT: should ONLY be called after all possible other propagations have been done:
 * the state has to be stable for both aggregate and unit propagations
 */
rClause IDSolver::notifypropagate() {
	if (!isInitialized() || !indirectPropagateNow()) {
		return nullPtrClause;
	}
/*
	//Testing new heuristic! => this implementation is TOO slow
	const vec<Lit>& trail = getPCSolver().getTrail();
	int recentindex = getPCSolver().getStartLastLevel();
	for (int i = recentindex; i < trail.size(); ++i) {
		const Var& v = var(trail[i]);
		if(originallyDefined(v) && (type(v)==DISJ)){
			const PropRule& r = *definition(v);
			for(int j=0; j<r.size(); ++j){
				getPCSolver().varBumpActivity(var(r[j]));
			}
		}
	}*/

	// There was an unfounded set saved which might not have been completely propagated by unit propagation
	// So check if there are any literals unknown and add more loopformulas
	if(savedufs.size()!=0){
		for(set<Var>::const_iterator i=savedufs.begin(); i!=savedufs.end(); ++i){
			if(!isFalse(*i)){
				Lit l = createNegativeLiteral(*i);
				addLoopfClause(l, savedloopf);
				return nullPtrClause;
			}
		}
		//none found:
		savedufs.clear();
	}

	if(!posloops){
		return nullPtrClause;
	}

	findCycleSources();

	if (css.size() == 0) {
		return nullPtrClause;
	}

	bool ufs_found = false;
	std::set<Var> ufs;
	int j = 0;
	uint64_t old_justify_calls = justify_calls;

	if (getPCSolver().modes().ufs_strategy == breadth_first) {
		for (vv::const_iterator j = css.begin(); !ufs_found && j < css.end(); ++j) {
			if (isCS(*j)) {
				ufs_found = unfounded(*j, ufs);
			}
		}
	} else {
		int visittime = 1; //time at which NO node has been visited yet
		vec<Var> stack;
		vector<Var> seen2;
		seen2.resize(nbvars, 0);
		/* the seen2 variable is used to indicate:
		 * 		that a value has been visited (and its number is the time at which it was visited
		 * 		0 means not yet visited
		 * 		a negative value means that it has been visited at the abs value and that it has
		 * 		already received a valid justification
		 */
		for (vv::const_iterator j = css.begin(); !ufs_found && j < css.end(); ++j) {//hij komt nooit in het geval dat hij iets op de stack moet pushen, altijd disj unfounded???
			if (isCS(*j) && seen(*j) == 0) {
				//om geen seen2 nodig te hebben, mag seen niet tegelijk gebruikt kunnen worden in unfounded()
				vec<vec<Lit> > network; //maps a node to a list of nodes that have visited the first one
				//as index, the visited time is used
				network.growTo(visittime + 1);
				network[visittime].push(mkLit(*j));
				UFS ret = visitForUFSsimple(*j, ufs, visittime, stack, seen2, network);
				switch (ret) {
					case UFSFOUND:
						ufs_found = true;
						break;
					case NOTUNFOUNDED:
						break;
					case STILLPOSSIBLE:
						break;
					case OLDCHECK:
						ufs_found = unfounded(*j, ufs);
						break;
				}
			}
		}
		for (int i = 0; i < nbvars; ++i) {
			seen2[i] = 0;
		}
	}

	justifiable_cycle_sources += ufs_found ? (j - 1) : j; // This includes those that are removed inside "unfounded".
	succesful_justify_calls += (justify_calls - old_justify_calls);

	rClause confl = nullPtrClause;
	if (ufs_found) {
		if (verbosity() >= 2) {
			report("Found an unfounded set of size %d: {",(int)ufs.size());
			for (std::set<Var>::const_iterator it = ufs.begin(); it != ufs.end(); ++it) {
				report(" %d",getPrintableVar(*it));
			}
			report(" }.\n");
		}
		++cycles;
		cycle_sizes += ufs.size();
		if (getPCSolver().modes().defn_strategy == adaptive) {
			++adaption_current; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
		}
		confl = assertUnfoundedSet(ufs);
	} else { // Found a witness justification.
		apply_changes();
	}

	return confl;
}

void IDSolver::notifyNewDecisionLevel() {
	if(posloops && modes().defn_strategy != adaptive && !isCycleFree()) {
		throw idpexception("Positive justification graph is not cycle free!\n");
	}
}

/**
 * Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void IDSolver::findCycleSources() {
	clearCycleSources();

	if (!backtracked || getPCSolver().modes().defn_strategy == always) {
		while(hasNextProp()){
			Lit l = getNextProp(); //l has become true, so find occurences of not l
			assert(value(not l)==l_False);
			if(nbvars <= var(l)){
				continue;
			}

			//TODO should check whether it is faster to use a real watched scheme here: go from justification to heads easily,
			//so this loop only goes over literal which are really justifications
			const vector<Var>& ds = disj_occurs(not l);
			for (vector<Var>::const_iterator j = ds.begin(); j < ds.end(); ++j) {
				checkJustification(*j);
			}

			vector<Var> heads = getDefAggHeadsWithBodyLit(var(not l));
			for (vv::const_iterator j = heads.begin(); j < heads.end(); ++j) {
				if(hasDefVar(*j)){
					checkJustification(*j);
				}
			}
		}
	} else { //Only if not always and backtracked
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		backtracked = false;
		for (vector<Var>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
			if (type(*i) == DISJ || type(*i) == AGGR) {
				checkJustification(*i);
			}
		}
	}
	if (verbosity() >= 2) {
		report("Indirect propagations. Verifying %zu cycle sources:",css.size());
		for (vv::const_iterator i = css.begin(); i < css.end(); ++i) {
			report(" %d", getPrintableVar(*i));
		}
		report(".\n");
	}
	++nb_times_findCS;
	cycle_sources += css.size();
}

void IDSolver::checkJustification(Var head) {
	if (!isDefInPosGraph(head) || isFalse(head) || isCS(head)) {
		return;
	}

	bool justfalse = false;
	for (int i = 0; !justfalse && i < justification(head).size(); ++i) {
		if (isFalse(justification(head)[i])) {
			justfalse = true;
		}
	}
	if (!justfalse) {
		return;
	}

	//Incorrect to prune out heads in which Lit is not the justification

	//Possible heuristic: getPCSolver().varBumpActivity(head);

	vec<Lit> jstf;
	bool external = true;

	if (type(head) == DISJ) {
		findJustificationDisj(head, jstf);
	} else {
		assert(type(head)==AGGR);
		findJustificationAggr(head, jstf);
	}
	for (int i = 0; external && i < jstf.size(); ++i) {
		if (isDefined(var(jstf[i])) && inSameSCC(head, var(jstf[i])) && isPositive(jstf[i])) {
			external = false;
		}
	}
	assert(jstf.size()>0);
	if (external) {
		changejust(head, jstf);
	} else {
		addCycleSource(head);
	}
}

/**
 * Looks for a justification for the given var. Attempts to find one that is not within the same positive dependency
 * graph scc (and certainly not false).
 */
void IDSolver::findJustificationDisj(Var v, vec<Lit>& jstf) {
	const PropRule& c = *definition(v);
	int pos = -1;
	for (int i = 0; i < c.size(); ++i) {
		if (!isFalse(c[i])) {
			pos = i;
			if (!inSameSCC(v, var(c[i])) || !isPositive(c[i]) || !isDefined(var(c[i]))) {
				break; //external justification is preferred.
			}
		}
	}
	assert(pos>=0);
	jstf.push(c[pos]);
}

/*
 * Return true if indirectpropagation is necessary. This is certainly necessary if the state is two-valued or if the strategy is always.
 */
bool IDSolver::indirectPropagateNow() {
	bool propagate = true;
	// if not always and state is three-valued.
	if (getPCSolver().modes().defn_strategy != always && !getPCSolver().totalModelFound()) {
		if (getPCSolver().modes().defn_strategy == lazy) {
			propagate = false;
		}
		if (getPCSolver().modes().defn_strategy == adaptive && adaption_current < adaption_total) {
			++adaption_current;
			propagate = false;
		}
	}
	return propagate;
}

/**
 * A loop is never introduced into the justification. If from the cycle source, no loop can be found,
 * the justification of the cycle source can be safely changed. If a loop is found, the cycle source becomes
 * false, so its justification can be kept to the original one, which will be correct when backtracking.
 */
bool IDSolver::unfounded(Var cs, std::set<Var>& ufs) {
	++justify_calls;
	vec<Var> tmpseen; // use to speed up the cleaning of data structures in "Finish"
	queue<Var> q;
	Var v;

	markNonJustified(cs, tmpseen);
	bool csisjustified = false;

	seen(cs) = 1; //no valid justification can be created just from looking at the body literals
	tmpseen.push(cs);

	if (verbosity() > 9) {
		for (vector<Var>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
			if (isJustified(*_seen, *i)) {
				report("Still justified %d\n", getPrintableVar(*i));
			}
		}
	}

	q.push(cs);
	ufs.clear();
	ufs.insert(cs);
	while (!csisjustified && q.size() > 0) {
		v = q.front();
		q.pop();
		if (isJustified(*_seen, v)) {
			continue;
		}
		if (directlyJustifiable(v, ufs, q)) {
			if (verbosity() > 5) {
				report("Can directly justify %d\n", getPrintableVar(v));
			}
			if (propagateJustified(v, cs, ufs)) {
				csisjustified = true;
			}
		}
	}

	for (int i = 0; i < tmpseen.size(); ++i) {
		seen(tmpseen[i]) = 0;
	}

#ifdef DEBUG
	for (auto i=defdVars.begin(); i!=defdVars.end(); ++i) { //seen should have been
		assert(seen(*i)==0);
	}
#endif

	if (!csisjustified) {
		assert(ufs.size() > 0); // The ufs atoms form an unfounded set. 'cs' is in it.
		return true;
	} else {
		ufs.clear();
		return false;
	}
}

/**
 * Important: to justify a head, often several body literals have to become FALSE
 * For such literals, they have to be justified if they are NEGATIVE
 *
 * Also, if a literal has to become FALSE, its INVERSION should be added to the justification!
 */
/**
 * seen is used as a justification mark/counter:
 *
 * seen==0 || negative body literal <=> justified
 */
inline bool IDSolver::isJustified(const InterMediateDataStruct& currentjust, Lit x) const {
	return isJustified(currentjust, var(x)) || !isPositive(x);
}
inline bool IDSolver::isJustified(const InterMediateDataStruct& currentjust, Var x) const {
	return currentjust.hasElem(x) && currentjust.getElem(x) == 0;
}
inline bool IDSolver::oppositeIsJustified(const InterMediateDataStruct& currentjust, const WL& l, bool real) const {
	if (real) {
		return value(l.getLit()) != l_True;
	} else {
		return value(l.getLit()) != l_True && (!sign(l.getLit()) || isJustified(currentjust, var(l.getLit())));
	}
}
inline bool IDSolver::isJustified(const InterMediateDataStruct& currentjust, const WL& l, bool real) const {
	if (real) {
		return value(l.getLit()) != l_False;
	} else {
		return value(l.getLit()) != l_False && (sign(l.getLit()) || isJustified(currentjust, var(l.getLit())));
	}
}

/**
 * Checks whether there is a justification for v given the current justification counters
 */
bool IDSolver::findJustificationDisj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf) {
	const PropRule& c = *definition(v);
	bool externallyjustified = false;
	seen(v) = 1;
	int pos = -1;
	for (int i = 0; !externallyjustified && i < c.size(); ++i) {
		if (c.getHead() == c[i]) {
			continue;
		}

		if (!isFalse(c[i])) {
			if (!isPositive(c[i]) || seen(var(c[i])) == 0) {
				if (!inSameSCC(v, var(c[i]))) {
					externallyjustified = true;
					pos = i;
				} else {
					pos = i;
				}
			} else {
				nonjstf.push(var(c[i]));
			}
		}
	}
	if (pos >= 0) {
		jstf.push(c[pos]);
		seen(v) = 0;
	}
	return seen(v) == 0;
}

bool IDSolver::findJustificationConj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf) {
	const PropRule& c = *definition(v);
	seen(v) = 0;
	for (int i = 0; i < c.size(); ++i) {
		if (isPositive(c[i]) && seen(var(c[i])) != 0) {
			++seen(v);
			nonjstf.push(var(c[i]));
		}
	}
	return seen(v) == 0;
}

bool IDSolver::findJustificationAggr(Var v, vec<Lit>& jstf, vec<Var>& nonjstf) {
	seen(v) = 1; //used as boolean (0 is justified, 1 is not)
	if (directlyJustifiable(v, jstf, nonjstf, *_seen)) {
		seen(v) = 0;
	}
	return seen(v) == 0;
}

/**
 * If the rule with head v can be justified, do that justification.
 * Otherwise, add all nonjustified body literals to the queue that have to be propagated (no negative body literals in a rule)
 *
 * @Post: v is now justified if a justification can be found based on the current seen vector
 * @Returns: true if v is now justified
 */
bool IDSolver::directlyJustifiable(Var v, std::set<Var>& ufs, queue<Var>& q) {
	vec<Lit> jstf;
	vec<Var> nonjstf;
	bool justified;

	switch (type(v)) {
		case CONJ:
			justified = findJustificationConj(v, jstf, nonjstf);
			break;
		case DISJ:
			justified = findJustificationDisj(v, jstf, nonjstf);
			break;
		case AGGR:
			justified = findJustificationAggr(v, jstf, nonjstf);
			break;
		default:
			assert(false);
			throw idpexception("The program tried to justify a rule that was not AGGR, DISJ or CONJ.\n");
	}
	if (justified) {
		assert(jstf.size()>0);
		changejust(v, jstf);
	} else {
		/*
		 * For conjunctive rules, it is not necessary to add all non-justified literals to the queue:
		 * one would be enough, as in the end all will have to be justified. Such a chosen literal would
		 * act as a watched literal: as long as it is not justified, the head cannot be justified. When it
		 * becomes justified, it should be checked whether there is another one not justified, which becomes
		 * the new watch.
		 * Maarten had such a "guards" system in the original code, but he claimed it complicated the code and
		 * had only a slight performance advantage and only on some benchmarks. It is commented in his original code.
		 */
		for (int i = 0; i < nonjstf.size(); ++i) {
			assert(!isJustified(*_seen, nonjstf[i]));
			if (inSameSCC(nonjstf[i], v)) {
				if (ufs.insert(nonjstf[i]).second) { //set insert returns true (in second) if the insertion worked (no duplicates)
					q.push(nonjstf[i]);
				}
			}
		}
	}
	return isJustified(*_seen, v);
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

		isCS(k) = false;
		++cs_removed_in_justify;

		if (k == cs) {
			return true;
		}

		Lit bdl = createPositiveLiteral(k);

		vec<Lit> heads;
		vec<vec<Lit> > jstf;
		propagateJustificationDisj(bdl, jstf, heads);
		propagateJustificationAggr(bdl, jstf, heads);

		for (int i = 0; i < heads.size(); ++i) {
			assert(jstf[i].size()>0);
			changejust(var(heads[i]), jstf[i]);
			justifiedq.push(var(heads[i]));
			if (verbosity() > 5) {
				report("justified %d\n", getPrintableVar(var(heads[i])));
			}
		}

		heads.clear();
		propagateJustificationConj(bdl, heads);
		for (int i = 0; i < heads.size(); ++i) {
			justifiedq.push(var(heads[i]));
			if (verbosity() > 5) {
				report("justified %d\n", getPrintableVar(var(heads[i])));
			}
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void IDSolver::changejust(Var v, vec<Lit>& just) {
	assert(just.size()>0 || type(v)==AGGR); //justification can be empty for aggregates
	justification(v).clear();
	just.copyTo(justification(v));
	for(int i=0; i<just.size(); ++i){
		getPCSolver().accept(this, not just[i], SLOW);
	}
}

/**
 * Given an unfounded sets, constructs the loop formula:
 * the set of all relevant external literals of the rules with heads in the unfounded set.
 */
void IDSolver::addExternalDisjuncts(const std::set<Var>& ufs,litlist& loopf) {
#ifdef DEBUG
	assert(loopf.size()==1); //Space for the head/new variable
	for (auto i=defdVars.begin(); i!=defdVars.end(); ++i) { //seen should be cleared
		assert(seen(*i)==0);
	}
#endif

	//In seen, we store literals that have been added to the loopf or found not to belong in it.
	//seen(A)==1 indicates that A has been added
	//seen(A)==2 indicates that not A has been added
	//Both can be added once, because of the assumption that a rule has been simplified to only contain any of them once

	for (std::set<Var>::const_iterator tch = ufs.begin(); tch != ufs.end(); ++tch) {
		switch (type(*tch)) {
			case CONJ: //
				break;
			case DISJ: {
				const PropRule& c = *definition(*tch);
				for (int i = 0; i < c.size(); ++i) {
					Lit l = c[i];
					if ((!isDefined(var(l)) || seen(var(l))!=(isPositive(l)?2:1)) && ufs.find(var(c[i])) == ufs.end()) {
						assert(isFalse(l));
						loopf.push_back(l);
						seen(var(l)) = (isPositive(l) ? 2 : 1);
					}
				}
				break;
			}
			case AGGR:
				addExternalLiterals(*tch, ufs, loopf, *_seen);
				break;
			default:
				assert(false);
				throw idpexception("Only AGGR, CONJ or DISJ should be checked for external disjuncts!\n");
				break;
		}
	}

	for (vsize i = 1; i < loopf.size(); ++i) {
		seen(var(loopf[i])) = 0;
	}
	extdisj_sizes += loopf.size() - 1;
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
 * Returns a non-owning pointer
 */
rClause IDSolver::assertUnfoundedSet(const std::set<Var>& ufs) {
	assert(!ufs.empty());

	// Create the loop formula: add the external disjuncts (first element will be filled in later).
	InnerDisjunction loopf;
	loopf.literals.push_back(mkLit(-1));
	addExternalDisjuncts(ufs, loopf.literals);

	// Check if any of the literals in the set are already true, which leads to a conflict.
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); ++tch) {
		if (isTrue(*tch)) {
			loopf.literals[0] = createNegativeLiteral(*tch); //negate the head to create a clause
			rClause c = getPCSolver().createClause(loopf, true);
			getPCSolver().addLearnedClause(c);
			++justify_conflicts;
			if (verbosity() >= 2) {
				report("Adding conflicting loop formula: [ ");
				MinisatID::print(c, getPCSolver());
				report("].\n");
			}
			//reportf("Conflicting unfounded set found.\n");
			return c;
		}
	}

	//Clasp only adds one asserting clause, assuming the other ones will be propagated.
	//There might be multiple loops => solution: save unfounded set and if propagate is called again and no backtrack has occurred, check if all have been propagated to be false, otherwise, add more clauses
	if(getPCSolver().modes().selectOneFromUFS){
		savedufs = ufs;
		savedloopf = loopf;
		Lit l = createNegativeLiteral(*ufs.begin());
		addLoopfClause(l, loopf);
	}else{
		// No conflict: then enqueue all facts and their loop formulas.
		if((long)(loopf.literals.size()*ufs.size())>modes().ufsvarintrothreshold){
			//introduce a new var to represent all external disjuncts: v <=> \bigvee external disj
			Var v = getPCSolver().newVar();
			if (verbosity() >= 2) {
				report("Adding new variable for loop formulas: %d.\n", getPrintableVar(v));
			}

			// not v \vee \bigvee\extdisj{L}
			addLoopfClause(createNegativeLiteral(v), loopf);

			// \forall d \in \extdisj{L}: not d \vee v
			InnerDisjunction binaryclause;
			binaryclause.literals = litlist{mkLit(-1), mkPosLit(v)};
			for (vsize i = 1; i < loopf.literals.size(); ++i) {
				addLoopfClause(not loopf.literals[i], binaryclause);
			}

			loopf.literals.resize(2);

			//the end loop formula just contains v
			loopf.literals[1] = createPositiveLiteral(v);
		}

		for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); ++tch) {
			Lit l = createNegativeLiteral(*tch);
			addLoopfClause(l, loopf);
		}
	}

	return nullPtrClause;
}

//Should make l false in the process
void IDSolver::addLoopfClause(Lit l, InnerDisjunction& lits) {
	lits.literals[0] = l;

	if (getPCSolver().modes().idclausesaving > 0) {
		if (value(lits.literals[0]) == l_Undef) {
#ifdef DEBUG
			for(vsize i=1; i<lits.literals.size(); ++i){
				assert(value(lits.literals[i])!=l_Undef);
				assert(getPCSolver().assertedBefore(var(lits.literals[i]), var(l)));
			}
#endif

			reason(var(l)) = lits.literals;
			getPCSolver().setTrue(lits.literals[0], this);
		}
	} else {
		rClause c = getPCSolver().createClause(lits, true);
		getPCSolver().addLearnedClause(c);

		//if unit propagation is already possible, this might not be detected on time, so help a little
		//MEANING: if lits is already completely false, this clause cannot be added to the store
		int unknown = 0;
		int unknindex = -1;
		bool allfalse = true;
		for (vsize i = 0; unknown < 2 && i < lits.literals.size(); ++i) {
			if (value(lits.literals[i]) == l_Undef) {
				++unknown;
				unknindex = i;
				allfalse = false;
			} else if (value(lits.literals[i]) == l_True) {
				allfalse = false;
			}
		}
		if (allfalse) {
			return;
		}

		if (unknown == 1) {
			getPCSolver().setTrue(lits.literals[unknindex], NULL, c);
		}

		if (verbosity() >= 2) {
			report("Adding loop formula: [ ");
			MinisatID::print(c, getPCSolver());
			report("].\n");
		}
	}

	assert(!isUnknown(l));
}

rClause IDSolver::getExplanation(const Lit& l) {
	assert(getPCSolver().modes().idclausesaving>0);
	InnerDisjunction clause;
	clause.literals = reason(var(l));
	return getPCSolver().createClause(clause, true);
}

/* Precondition:  seen(i)==0 for each i.
 * Postcondition: seen(i)  for exactly those i that are ancestors of cs in sp_justification. If modes.defn_search==stop_at_cs, there should not be other cycle sources then cs in the path from added literals to cs.
 */
void IDSolver::markNonJustified(Var cs, vec<Var>& tmpseen) {
	queue<Var> q;
	markNonJustifiedAddParents(cs, cs, q, tmpseen);
	// Now recursively do the same with each enqueued Var.
	Var x;
	while (q.size() > 0) {
		x = q.front();
		q.pop();
		markNonJustifiedAddParents(x, cs, q, tmpseen);
	}
}

void IDSolver::markNonJustifiedAddParents(Var x, Var cs, queue<Var> &q, vec<Var>& tmpseen) {
	Lit poslit = createPositiveLiteral(x);
	if(hasdisj_occurs(poslit)){
		const vector<Var>& v = disj_occurs(poslit);
		for (vector<Var>::const_iterator i = v.begin(); i < v.end(); ++i) {
			if (isDefInPosGraph(*i) && var(justification(*i)[0]) == x) {
				markNonJustifiedAddVar(*i, cs, q, tmpseen);
			}
		}
	}
	if(hasconj_occurs(poslit)){
		const vector<Var>& w = conj_occurs(poslit);
		for (vector<Var>::const_iterator i = w.begin(); i < w.end(); ++i) {
			markNonJustifiedAddVar(*i, cs, q, tmpseen);
		}
	}
	vector<Var> heads = getDefAggHeadsWithBodyLit(x);
	for (vector<Var>::size_type i = 0; i < heads.size(); ++i) {
		vec<Lit>& jstfc = justification(heads[i]);
		for (int k = 0; k < jstfc.size(); ++k) {
			if (jstfc[k] == poslit) { // Found that x is actually used in y's justification.
				markNonJustifiedAddVar(heads[i], cs, q, tmpseen);
				break;
			}
		}
	}
}

inline void IDSolver::markNonJustifiedAddVar(Var v, Var cs, queue<Var> &q, vec<Var>& tmpseen) {
	// TODO prove whether this false can be here?
	if (/*!isFalse(v) && */ inSameSCC(v, cs) && (getPCSolver().modes().defn_search == include_cs || v == cs || !isCS(v))) {
		if (seen(v) == 0) {
			seen(v) = 1;
			tmpseen.push(v);
			q.push(v);
			++total_marked_size;
		} else {
			++seen(v);
		}

		if (verbosity() > 9) {
			report("Not justified %d, times %d\n", getPrintableVar(v), seen(v));
		}
	}
}

/**
 * Propagates the changes from supporting to cycle free
 */
inline void IDSolver::apply_changes() {
	if (getPCSolver().modes().defn_strategy == adaptive) {
		if (adaption_current == adaption_total) {
			++adaption_total; // Next time, skip one decision level extra.
		} else {
			adaption_total--;
		}
		if (adaption_total < 0) {
			adaption_total = 0;
		}
		adaption_current = 0;
	}
}

/*********************
 * AGGSOLVER METHODS *
 *********************/

const vec<Lit>& IDSolver::getCFJustificationAggr(Var v) const {
	return justification(v);
}

/**
 * Checks whether the aggregate head v has a new external justification (just).
 * If this is the case (all literal in other scc than v or not defined in pos graph), then the new just is added.
 * Otherwise, v is added as a cycle source.
 */
void IDSolver::cycleSourceAggr(Var v, vec<Lit>& just) {
	bool alljustifiedexternally = true;
	for (int i = 0; alljustifiedexternally && i < just.size(); ++i) {
		if (isDefInPosGraph(var(just[i])) && inSameSCC(v, var(just[i]))) {
			alljustifiedexternally = false;
		}
	}
	if (!alljustifiedexternally) {
		addCycleSource(v);
	} else {
		assert(just.size()>0);
		changejust(v, just);
	}
}

inline void IDSolver::print(const PropRule& c) const {
	report("Rule ");
	Lit head = c.getHead();
	MinisatID::print(head, value(head));
	report(" <- ");
	for (int i = 0; i < c.size(); ++i) {
		MinisatID::print(c[i], value(c[i]));
		fprintf(stderr, " ");
	}
	report("\n");
}

/**
 * Checks if there are any positive loops in the current dependecy graph. Mainly used for debugging purposes (does slow bottom-up reasoning)
 */
bool IDSolver::isCycleFree() const {
	if(!modes().checkcyclefreeness){ //TODO can never be set to true!
		return true;
	}
#ifdef DEBUG
	for (int i = 0; i < nbvars; ++i) {
		assert(!isDefined(i) || justification(i).size()>0 || type(i)!=DISJ || occ(i)==MIXEDLOOP);
	}
#endif
	if (hasRecursiveAggregates()) {
		if (verbosity() >= 2) {
			report("Cycle-freeness checking is not implemented in the presence of recursive aggregates.\n");
		}
		return true;
	}

	if (verbosity() >= 2) {
		report("Showing justification for disjunctive atoms. <<<<<<<<<<\n");
		for (int i = 0; i < nbvars; ++i) {
			if (isDefined(i) && type(i) == DISJ && occ(i) != MIXEDLOOP) {
				clog <<mkLit(i, false) <<"<-" <<justification(i)[0] <<"; ";
			}
		}
		report(">>>>>>>>>>\n");
	}

	// Verify cycles.
	vector<Var> isfree(nbvars, 0); // per variable. 0 = free, >0 = number of literals in body still to be justified.
	vector<Lit> justified;
	int cnt_nonjustified = 0;
	for (int i = 0; i < nbvars; ++i) {
		justified.push_back(mkLit(i, true)); // negative literals are justified anyhow.
		if (!isDefInPosGraph(i)) {
			justified.push_back(mkLit(i, false));
		} else {
			++cnt_nonjustified;
			isfree[i] = type(i) == CONJ ? definition(i)->size() : 1;

			if (type(i) == DISJ) {
				if (value(i) == l_True) {
					assert(value(justification(i)[0])!=l_False);
				} else {
					for (int j = 0; j < definition(i)->size(); ++j) {
						assert(value(definition(i)->operator [](j))!=l_True);
					}
				}
			} else {
				if (value(i) == l_True) {
					for (int j = 0; j < definition(i)->size(); ++j) {
						assert(value(definition(i)->operator [](j))!=l_False);
					}
				} else {
					bool found = false;
					for (int j = 0; !found && j < definition(i)->size(); ++j) {
						if (value(definition(i)->operator [](j)) != l_True) {
							found = true;
						}
					}
					assert(found);
				}

			}
		}
	}

	if (cnt_nonjustified == 0) {
		return true;
	}

	uint idx = 0;
	while (cnt_nonjustified > 0 && idx < justified.size()) {
		const Lit& l = justified[idx++];

		/*
		 vec<Var> as;
		 if(getAggSolver()!=NULL){
		 getAggSolver()->getHeadsOfAggrInWhichOccurs(var(l), as);
		 }
		 */

		//occ as disjunctively justifying literal
		if(hasdisj_occurs(l)){
			const vector<Var>& ds = disj_occurs(l);
			for (vector<Var>::const_iterator i = ds.begin(); i < ds.end(); ++i) {
				Var d = *i;
				assert(type(d)==DISJ && (!isDefInPosGraph(*i) || justification(d).size()==1));
				if (isfree[d] > 0 && justification(d)[0] == l) {
					assert(isfree[d]==1);
					isfree[d] = 0;
					justified.push_back(mkLit(d, false));
					--cnt_nonjustified;
				}
			}
		}

		if(hasconj_occurs(l)){
			const vector<Var>& cs = conj_occurs(l);
			for (vector<Var>::const_iterator i = cs.begin(); i < cs.end(); ++i) {
				Var c = *i;
				assert(type(c)==CONJ);
				if (isfree[c] > 0) {
					isfree[c]--;
					if (isfree[c] == 0) {
						justified.push_back(mkLit(c, false));
						--cnt_nonjustified;
					}
				}
			}
		}

		/*
		 for (int i=0;i<as.size();++i) {
		 Var d = as[i];
		 bool found = false;
		 for(int j=0; j<justification[d].size(); ++j){
		 if (justification[d][j]==l && isfree[d]>0) {
		 found = true;
		 break;
		 }
		 }
		 if(found){
		 isfree[d]--;
		 if (isfree[d]==0) {
		 justified.push(mkLit(d,false));
		 --cnt_nonjustified;
		 }
		 }
		 }
		 */
	}

	if (cnt_nonjustified > 0) {
		if (verbosity() > 2) {
			report("WARNING: There remain %d literals non-justified.\n",cnt_nonjustified);
		}

		vec<bool> printed;
		printed.growTo(nbvars, false);
		int i = 0;
		while (i < nbvars) {
			if (verbosity() > 2) {
				report("Cycle:\n");
			}
			for (; i < nbvars && (!isDefInPosGraph(i) || isfree[i] == 0); ++i)
				;

			if (i < nbvars) {
				vec<Var> cycle;
				cycle.push(i);
				int idx = 0;
				while (idx < cycle.size()) {
					Var v = cycle[idx++];
					if (type(v) == DISJ) {
						if (verbosity() >= 2) {
							clog <<"D " <<getPrintableVar(v) <<" justified by " <<justification(v)[0] <<".\n";
						}
						if (!printed[var(justification(v)[0])]) {
							cycle.push(var(justification(v)[0]));
						}
					} else if (type(v) == CONJ) {
						if (verbosity() > 2) {
							report("C %d has", getPrintableVar(v));
						}
						const PropRule& c = *definition(v);
						for (int j = 0; j < c.size(); ++j) {
							Var vj = var(c[j]);
							if (c[j] != c.getHead() && isPositive(c[j]) && (isfree[vj] != 0 || printed[vj])) {
								if (verbosity() > 2) {
									report(" %d", getPrintableVar(vj));
								}
								if (!printed[vj]) {
									cycle.push(vj);
								}
							}
						}
						if (verbosity() > 2) {
							report(" in its body.\n");
						}
					} else {
						if (verbosity() > 2) {
							report("Change aggregate output here (iscyclefree method)");
							//TODO change output
						}
					}
					printed[v] = true;
				}
				for (int j = 0; j < cycle.size(); ++j) {
					isfree[cycle[j]] = 0;
				}
			}
		}
	} else {
		if (verbosity() > 2) {
			report("OK; justification is cycle free.\n");
		}
	}
	return cnt_nonjustified == 0;
}

rClause IDSolver::notifyFullAssignmentFound(){
	rClause confl = notifypropagate();
	if(confl==nullPtrClause && getSemantics()==DEF_WELLF){
		confl = isWellFoundedModel();
	}
	return confl;
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
 * TODO currently no well founded model checking over aggregates
 * this can be done by implementing wf propagation and counter methods in aggregates.
 */
rClause IDSolver::isWellFoundedModel() {
	if(getSemantics()!=DEF_WELLF){
		throw idpexception("Should not be checking for well-founded model, because mode is stable semantics!\n");
	}

#ifdef DEBUG
	if (posloops && !isCycleFree()) {
		if (verbosity() > 1) {
			report("A positive unfounded loop exists, so not well-founded!\n");
		}
		return nullPtrClause;
	}
#endif

	if (!negloops) {
		if (verbosity() > 1) {
			report("Well-founded for positive loops, no negative loops present!\n");
		}
		return nullPtrClause;
	}

	if(mixedrecagg){
		throw idpexception("For recursive aggregates, only stable semantics is currently supported! Wellfoundedness is not checked\n");
	}

	// Initialize scc of full dependency graph
	//TODO also here use reduce memory overhead by only using it for defined variables!
	wfroot.resize(nbvars, -1);
	vector<Var> rootofmixed;
	wfisMarked.resize(nbvars, false);

	findMixedCycles(wfroot, rootofmixed);

	if (verbosity() > 1) {
		report("general SCCs found");
		for (vector<int>::size_type z = 0; z < wfroot.size(); ++z) {
			report("%d has root %d\n", getPrintableVar(z), getPrintableVar(wfroot[z]));
		}
		report("Mixed cycles are %s present.\n", rootofmixed.empty()?"not":"possibly");
	}

	if (rootofmixed.empty()) {
		if (verbosity() > 1) {
			report("The model is well-founded!\n");
		}
		return nullPtrClause;
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
	while (!wffixpoint) {
		wffixpoint = true;

		initializeCounters();
		forwardPropagate(true);
		if (wfmarkedAtoms.empty()) {
			if (verbosity() > 1) {
				report("The model is well-founded!\n");
			}
			return nullPtrClause;
		}
		overestimateCounters();
		forwardPropagate(false);
		removeMarks();
		if (wfmarkedAtoms.empty()) {
			if (verbosity() > 1) {
				report("The model is well-founded!\n");
			}
			return nullPtrClause;
		}
	}

	for (int i = 0; i < nbvars; ++i) {
		seen(i) = 0;
	}

	if (verbosity() > 1) {
		report("The model is not well-founded!\n");
	}

	//Returns the found assignment (TODO might be optimized to just return the loop)
	const vector<Lit>& decisions = getPCSolver().getDecisions();
	InnerDisjunction invalidation;
	for(vector<Lit>::const_iterator i=decisions.begin(); i<decisions.end(); ++i){
		invalidation.literals.push_back(not (*i));
	}
	rClause confl = getPCSolver().createClause(invalidation, true);
	getPCSolver().addLearnedClause(confl);
	return confl;
}

/**
 * Visit the heads of all rules and check the current JUSTIFICATION graph for loops with mixed signs
 * (because of standard propagation, there are no other loops). The head is always positive,
 * so pure negative loops are not possible.
 */
void IDSolver::findMixedCycles(vector<Var> &root, vector<int>& rootofmixed) {
	vector<bool> incomp(nbvars, false);
	stack<Var> stack;
	vector<int> visited(nbvars, 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	int counter = 1;

	for (vector<Var>::const_iterator i = defdVars.begin(); i < defdVars.end(); ++i) {
		Var v = *i;
		if (visited[v] == 0) {
			visitWF(v, root, incomp, stack, visited, counter, true, rootofmixed);
		}
	}
}

void IDSolver::visitWF(Var v, vector<Var> &root, vector<bool> &incomp, stack<Var> &stack, vector<Var> &visited,
		int& counter, bool throughPositiveLit, vector<int>& rootofmixed) {
	assert(!incomp[v]);
	assert(isDefined(v));
	++counter;
	visited[v] = throughPositiveLit ? counter : -counter;
	root[v] = v;
	stack.push(v);

	bool headtrue = value(v) == l_True;

	if (type(v) == AGGR) {
		/*vec<Lit> lits;
		 aggsolver->getLiteralsOfAggr(v, lits);
		 for(int i=0; i<lits.size(); ++i){
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
	} else if ((headtrue && isConjunctive(v)) || (!headtrue && isDisjunctive(v))) {
		//head is false and disj, or head is true and conj: all body literals are its justification
		for (int i = 0; i < definition(v)->size(); ++i) {
			Lit l = definition(v)->operator [](i);
			Var w = var(l);
			if (!isDefined(w)) {
				continue;
			}
			if (visited[w] == 0) {
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			} else if (!incomp[w] && !isPositive(l) && visited[v] > 0) {
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]]) > abs(visited[root[w]])) {
				root[v] = root[w];
			}
		}
	} else {//head is true and DISJ or head is false and CONJ: one literal is needed for justification
		// for DISJ, the justification is already known TODO INCORRECT when no pos loops possible over head!
		// for a CONJ, randomly choose one of the false body literals. If there is no loop through it, then it is a good choice.
		//			If there is, it will be found later if another false literal exists without a mixed loop.
		Lit l = mkLit(-1);
		if (isConjunctive(v)) {
			for (int i = 0; i < definition(v)->size(); ++i) {
				Lit l2 = definition(v)->operator [](i);
				if (isFalse(l2)) {
					l = l2;
					break;
				}
			}
		} else {
			for (int i = 0; i < definition(v)->size(); ++i) {
				Lit l2 = definition(v)->operator [](i);
				if (isTrue(l2)) {
					l = l2;
					break;
				}
			}
		}
		assert(var(l)>-1);
		Var w = var(l);
		if (isDefined(w)) {
			if (visited[w] == 0) {
				visitWF(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed);
			} else if (!incomp[w] && !isPositive(l) && visited[v] > 0) {
				visited[v] = -visited[v];
			}
			if (!incomp[w] && abs(visited[root[v]]) > abs(visited[root[w]])) {
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
			visited[w] < 0 ? mixed = true : true;
			root[w] = v; //these are the found sccs
			incomp[w] = true;
		} while (w != v);
		if (mixed) {
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
	Lit l = mkLit(h, isFalse(h)); //holds the literal that has to be propagated, so has the model value
	if (!wfisMarked[h]) {
		wfqueue.push(l);
		wfisMarked[h] = true;
		wfmarkedAtoms.insert(h);
	}
}

/**
 * marks all literals that can be reached upwards from the cycle roots.
 */
void IDSolver::markUpward() {
	for (vector<Var>::size_type n = 0; n < wfrootnodes.size(); ++n) {
		Var temp = wfrootnodes[n];
		mark(temp);
	}

	while (!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		if(hasconj_occurs(l)){
			for (vv::const_iterator i = conj_occurs(l).begin(); i < conj_occurs(l).end(); ++i) {
				mark(*i);
			}
		}
		if(hasdisj_occurs(l)){
			for (vv::const_iterator i = disj_occurs(l).begin(); i < disj_occurs(l).end(); ++i) {
				mark(*i);
			}
		}

		l = not l;

		if(hasconj_occurs(l)){
			for (vv::const_iterator i = conj_occurs(l).begin(); i < conj_occurs(l).end(); ++i) {
				mark(*i);
			}
		}
		if(hasdisj_occurs(l)){
			for (vv::const_iterator i = disj_occurs(l).begin(); i < disj_occurs(l).end(); ++i) {
				mark(*i);
			}
		}


		/*TODO? if(aggsolver!=NULL){
		 vec<Lit> heads;
		 aggsolver->getHeadsOfAggrInWhichOccurs(var(l), heads);
		 for(int i=0; i<heads.size(); ++i){
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
	for (set<Var>::iterator i = wfmarkedAtoms.begin(); i != wfmarkedAtoms.end(); ++i) {
		Var v = *i;
		seen(v) = 0;
		bool canbepropagated = false;
		for (int j = 0; !canbepropagated && j < definition(v)->size(); ++j) {
			Lit bl = definition(v)->operator [](j);
			if (wfisMarked[var(bl)]) {
				++seen(v);
			} else if (isFalse(bl) && type(v) == CONJ) {
				canbepropagated = true;
			} else if (isTrue(bl) && type(v) == DISJ && var(bl) != v) {
				canbepropagated = true;
			}
		}
		if (seen(v) == 0 || canbepropagated) {
			seen(v) = 0;
			wfqueue.push(isTrue(v) ? createPositiveLiteral(v) : createNegativeLiteral(v));
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
	while (!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		if (!wfisMarked[var(l)]) {
			continue;
		}
		wfisMarked[var(l)] = false;

		if (removemarks) {
			wfmarkedAtoms.erase(var(l));
			wffixpoint = false;
		}

		//Literal l has become true, so for all rules with body literal l and marked head,
		//if DISJ, then head will be true, so add true head to queue and set counter to 0
		if(hasdisj_occurs(l)){
			for (vv::const_iterator i = disj_occurs(l).begin(); i < disj_occurs(l).end(); ++i) {
				Var head = *i;
				if (wfisMarked[head]) {
					wfqueue.push(createPositiveLiteral(head));
					seen(head) = 0;
				}
			}
		}

		if(hasconj_occurs(l)){
			//if CONJ and counter gets 0, then head will be true, so add true head to queue
			for (vv::const_iterator i = conj_occurs(l).begin(); i < conj_occurs(l).end(); ++i) {
				Var head = *i;
				if (wfisMarked[head] && --seen(head) == 0) {
					wfqueue.push(createPositiveLiteral(head));
				}
			}
		}


		l = not l;

		//Literal l has become false, so for all rules with body literal l and marked head,
		//if DISJ and counter gets 0, then head will be false, so add false head to queue
		if(hasdisj_occurs(l)){
			for (vv::const_iterator i = disj_occurs(l).begin(); i < disj_occurs(l).end(); ++i) {
				Var head = *i;
				if (wfisMarked[head] && --seen(head) == 0) {
					wfqueue.push(createNegativeLiteral(head));
				}
			}
		}

		//if CONJ, then head will be false, so add false head to queue and set counter to 0
		if(hasconj_occurs(l)){
			for (vv::const_iterator i = conj_occurs(l).begin(); i < conj_occurs(l).end(); ++i) {
				Var head = *i;
				if (wfisMarked[head]) {
					wfqueue.push(createNegativeLiteral(head));
					seen(head) = 0;
				}
			}
		}

		//TODO AGGREGATES
	}
}

/**
 * Overestimate the counters by making all negative defined marked body literals true.
 */
void IDSolver::overestimateCounters() {
	for (set<Var>::iterator i = wfmarkedAtoms.begin(); i != wfmarkedAtoms.end(); ++i) {
		Var v = *i;
		assert(seen(v) > 0);

		for (int j = 0; j < definition(v)->size(); ++j) {
			Lit bdl = definition(v)->operator [](j);
			if (wfisMarked[var(bdl)] && !isPositive(bdl) && v != var(bdl)) {
				if (type(v) == CONJ) {
					seen(v)--;
				} else {
					seen(v) = 0;
				}
			}
		}

		if (seen(v) == 0) {
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
	for (set<Var>::iterator i = wfmarkedAtoms.begin(); i != wfmarkedAtoms.end(); ++i) {
		Var v = *i;
		if (wfisMarked[v]) {
			temp.push(v);
			wfisMarked[v] = false;
			wffixpoint = false;
		} else {
			wfisMarked[v] = true;
		}
	}
	while (!temp.empty()) {
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
void IDSolver::changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, VarToJustif& vis) {
	vec<Lit> queue;

	if (!hasJustificationTarjan(definednode, vis)) {
		vec<Lit> j;
		j.push(firstjustification);
		changejust(definednode, j);
		vis[definednode] = -vis[definednode]; //set it as justified
		queue.push(mkLit(definednode));
	}

	while (queue.size() > 0) {
		Lit just = queue.last();
		queue.pop();
		for (int i = 0; i < network[visitedAtTarjan(var(just), vis)].size(); ++i) {
			Lit t = network[visitedAtTarjan(var(just), vis)][i];
			if (!hasJustificationTarjan(var(t), vis)) {
				vec<Lit> j;
				j.push(just);
				changejust(var(t), j);
				vis[var(t)] = -vis[var(t)];
				queue.push(t);
			}
		}
	}
}

inline bool IDSolver::visitedEarlierTarjan(Var x, Var y, const VarToJustif& vis) const {
	int x1 = vis[x] > 0 ? vis[x] : -vis[x];
	int y1 = vis[y] > 0 ? vis[y] : -vis[y];
	return x1 < y1;
}

inline bool IDSolver::visitedTarjan(Var x, const VarToJustif& vis) const {
	return vis[x] != 0;
}

inline int IDSolver::visitedAtTarjan(Var x, const VarToJustif& vis) const {
	return vis[x] > 0 ? vis[x] : -vis[x];
}

inline bool IDSolver::hasJustificationTarjan(Var x, const VarToJustif& vis) const {
	return vis[x] < 0;
}

/////////////
//Finding unfounded checks by
//validjust indicates both that the element is already in a justification or is in another found component (in which case it might also be false, not requiring a justification)
//TODO aggregates
UFS IDSolver::visitForUFSsimple(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, VarToJustif& vis, vec<vec<Lit> >& network) {
	vis[v] = visittime;
	int timevisited = visittime;
	++visittime;

	DefType t = type(v);
	if (t == AGGR) {
		return OLDCHECK;
	}
	assert(t==CONJ || t==DISJ);

	PropRule const * const c = definition(v);
	if (verbosity() >= 1) {
		print(*c);
	}

	Lit definedChild;
	bool childfound = false;

	for (int i = 0; i < c->size(); ++i) {
		DefType childtype = type(var(c->operator [](i)));
		Lit l = c->operator [](i);
		if (var(l) == v) {
			continue;
		} //rule head or identical body atom
		if (childtype == AGGR) {
			return OLDCHECK;
		}
		if (!isDefInPosGraph(var(c->operator [](i))) || !inSameSCC(var(l), v) || hasJustificationTarjan(var(l),	vis)) {
			if (!isFalse(l) && t == DISJ) {
				changeJustificationsTarjan(v, l, network, vis);
				return NOTUNFOUNDED;
			}
		}
		if (t == CONJ) {
			if (childfound) {
				definedChild = l;
				childfound = true;
			} else {
				return OLDCHECK;
			}
		}
	}

	stack.push(v);

	if (t == CONJ) {
		if (childfound) {
			if (visitedTarjan(var(definedChild), vis)) {
				network.growTo(visittime + 1);
				network[visittime].push(mkLit(v));
			} else {
				network[visitedAtTarjan(var(definedChild), vis)].push(mkLit(v));
			}

			if (!visitedTarjan(var(definedChild), vis)) {
				UFS ret = visitForUFSsimple(var(definedChild), ufs, visittime, stack, vis, network);
				if (ret != STILLPOSSIBLE) {
					return ret;
				}
			}
			if (!hasJustificationTarjan(var(definedChild), vis) && visitedEarlierTarjan(var(definedChild), v, vis)) {
				vis[v] = vis[var(definedChild)];
			}
		}
	} else { //DISJ, have returned from all others
		for (int i = 0; i < c->size(); ++i) {
			Var child = var(c->operator [](i));
			if (child == v) {
				continue;
			}
			if (!(type(child) == CONJ || type(child) == DISJ)) {
				continue;
			}

			if (!visitedTarjan(child, vis)) {
				network.growTo(visittime + 1);
				network[visittime].push(mkLit(v));
			} else {
				network[visitedAtTarjan(child, vis)].push(mkLit(v));
			}

			if (!visitedTarjan(child, vis)) {
				UFS ret = visitForUFSsimple(child, ufs, visittime, stack, vis, network);
				if (ret != STILLPOSSIBLE) {
					return ret;
				}
			}
			if (!hasJustificationTarjan(child, vis) && visitedEarlierTarjan(child, v, vis)) {
				vis[v] = vis[child];
			}
		}
	}

	if (visitedAtTarjan(v, vis) == timevisited) {
		bool allfalse = true;
		Var x;
		do {
			x = stack.last();
			stack.pop();
			vis[x] = vis[x] > 0 ? vis[x] : -vis[x];
			ufs.insert(x);
			if (!isFalse(x)) {
				allfalse = false;
			}
		} while (x != v);
		if (allfalse) {
			ufs.clear();
			return STILLPOSSIBLE;
		}
		if (ufs.size() > 1) {
			if (verbosity() >= 4) {
				fprintf(stderr, "ufsfound: ");
				for (std::set<Var>::iterator i = ufs.begin(); i != ufs.end(); ++i) {
					Var x = *i;
					fprintf(stderr, "%d:%c", x << 1, isTrue(x) ? '1' : (isFalse(x) ? '0' : 'X'));
				}
				fprintf(stderr, "\n");
			}
			return UFSFOUND;
		} else {
			int containsx = 0;
			for (int i = 0; i < c->size(); ++i) {
				if (x == var(c->operator [](i))) {
					++containsx;
				}
			}
			if (containsx > 1) { //there is a loop of length 1, so x itself is an UFS
				if (verbosity() >= 4) {
					fprintf(stderr, "ufsfound: ");
					for (std::set<Var>::iterator i = ufs.begin(); i != ufs.end(); ++i) {
						Var x = *i;
						fprintf(stderr, "%d:%c", x << 1, isTrue(x) ? '1' : (isFalse(x) ? '0' : 'X'));
					}
					fprintf(stderr, "\n");
				}
				return UFSFOUND;
			} else {//no loops, x is only an SCC, not a UFS
				ufs.clear();
			}
		}
	}

	return STILLPOSSIBLE;
}

// PRINT INFORMATION

void IDSolver::printState() const{
	MinisatID::print(this);
}


void IDSolver::printStatistics() const {
	report("> cycles                : %-12" PRIu64 "\n", cycles);
	report("> cycle conflicts       : %-12" PRIu64 "\n", justify_conflicts);
	report("> avg cycle size        : %4.2f\n", (float)cycle_sizes/cycles);
	report("> avg extdisj size      : %4.2f\n", (float)extdisj_sizes/cycles);
	report("> justify runs          : %-12" PRIu64 "   (%4.2f /cycle)\n", justify_calls, (float)justify_calls/cycles);
	report("> avg. justify searchsp.: %6.2f lits\n", (float)total_marked_size/justify_calls);
	report("> cycle sources         : %-12" PRIu64 "\n", cycle_sources);
	report(">                       : %4.2f found per run of findCycleSources()\n", (float)nb_times_findCS/cycle_sources);
	report(">                       : %4.2f removed per justify run\n", (float)cs_removed_in_justify/justify_calls);
	report(">                       : %4.2f treated per loop\n", (float)succesful_justify_calls/nb_times_findCS);
}

AggProp const * getProp(AggType type){
	switch(type){
		case MAX: return AggProp::getMax();
		case SUM: return AggProp::getSum();
		case PROD: return AggProp::getProd();
		case CARD: return AggProp::getCard();
		default: assert(false); break;
	}
}

bool IDSolver::canJustifyHead(const IDAgg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	if(agg.getType()==MAX){
		return canJustifyMaxHead(agg, jstf, nonjstf, currentjust, real);
	}else{
		assert(agg.getType()==PROD || agg.getType()==SUM || agg.getType()==CARD);
		return canJustifySPHead(agg, jstf, nonjstf, currentjust, real);
	}
}

bool IDSolver::canJustifyMaxHead(const IDAgg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	bool justified = true;
	const vwl& wl = agg.getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && i->getWeight() > agg.getBound(); ++i) {
			if (oppositeIsJustified(currentjust, *i, real)) {
				jstf.push(not i->getLit()); //push negative literal, because it should become false
			} else if (real || currentjust.getElem(var(i->getLit())) != 0) {
				nonjstf.push(var(i->getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	}

	if(justified && agg.hasLB()){
		justified = false;
		for (vwl::const_reverse_iterator i = wl.rbegin(); i < wl.rend() && i->getWeight() >= agg.getBound(); ++i) {
			if (isJustified(currentjust, *i, real)) {
				jstf.push(i->getLit());
				justified = true;
			} else if (real || (currentjust.hasElem(var(i->getLit())) && currentjust.getElem(var(i->getLit())) != 0)) {
				nonjstf.push(var(i->getLit()));
			}
		}
	}

	if (!justified) {
		jstf.clear();
	}

	return justified;
}

/**
 * AGG <= B: v is justified if one literal below/eq the bound is THAT IS NOT THE HEAD
 * 					if so, change the justification to the literal
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 * A <= AGG: v is justified if the negation of all literals below the bound are. The emptyset is always a solution,
 * 			 so no conclusions have to be drawn from the literals above/eq the bound
 * 					if so, change the justification to the negation of all those below the bound literals
 * 					otherwise, add all nonfalse, non-justified, relevant, below the bound literals to the queue
 */
bool IDSolver::canJustifySPHead(const IDAgg& agg, vec<Lit>& jstf, vec<Var>& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	const AggProp& type = *getProp(agg.getType());
	bool justified = true;
	const vwl& wl = agg.getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		Weight bestpossible = type.getMaxPossible(wl);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (oppositeIsJustified(currentjust, *i, real)) {
				jstf.push(not i->getLit());
				bestpossible = type.remove(bestpossible, i->getWeight());
				if (bestpossible <= agg.getBound()) {
					justified = true;
				}
			} else if (real || currentjust.getElem(var(i->getLit())) != 0) {
				nonjstf.push(var(i->getLit()));
			}
		}
	}
	if(justified && agg.hasLB()){
		justified = false;
		Weight bestcertain = type.getMinPossible(wl);
		for (vwl::const_iterator i = wl.begin(); !justified && i < wl.end(); ++i) {
			if (isJustified(currentjust, *i, real)) {
				jstf.push(i->getLit());
				bestcertain = type.add(bestcertain, i->getWeight());
				if (bestcertain >= agg.getBound()) {
					justified = true;
				}
			} else if (real || (currentjust.hasElem(var(i->getLit())) && currentjust.getElem(var(i->getLit())) != 0)) {
				nonjstf.push(var(i->getLit()));
			}
		}
	}

	if (!justified) {
		jstf.clear();
	}

	return justified;
}

IDAgg* IDSolver::getAggDefiningHead(Var v) const {
	//FIXME checks en mooiere code
	return aggdefinition(v);
}

vector<Var> IDSolver::getDefAggHeadsWithBodyLit(Var x) const{
	vector<Var> heads;
	for (vector<Var>::const_iterator i = aggr_occurs(mkLit(x)).begin(); i < aggr_occurs(mkLit(x)).end(); ++i) {
		heads.push_back(var(aggdefinition(*i)->getHead()));
	}
	return heads;
}

vwl::const_iterator IDSolver::getSetLitsOfAggWithHeadBegin(Var x) const {
	return getAggDefiningHead(x)->getWL().begin();
}

vwl::const_iterator IDSolver::getSetLitsOfAggWithHeadEnd(Var x) const {
	return getAggDefiningHead(x)->getWL().end();
}

/**
 * For an aggregate expression defined by v, add all set literals to loopf that
 * 		- have not been added already(seen[A]==1 for A, seen[A]==2 for not A)
 * 		- might help to make the expression true (monotone literals!) (to make it a more relevant learned clause)
 * Currently CONSIDERABLE overapproximation: take all known false literals which are set literal or its negation,
 * do not occur in ufs and have not been seen yet.
 * Probably NEVER usable external clause!
 * TODO: optimize: add monotone literals until the aggregate can become true
 */
void IDSolver::addExternalLiterals(Var v, const std::set<Var>& ufs, litlist& loopf, InterMediateDataStruct& seen) {
	for (vwl::const_iterator i = getAggDefiningHead(v)->getWL().begin(); i < getAggDefiningHead(v)->getWL().end(); ++i) {
		Lit l = i->getLit();
		if(ufs.find(var(l)) != ufs.end() || seen.getElem(var(l)) == (isPositive(l) ? 2 : 1)){
			continue;
		}

		if(isTrue(l)){
			l = not l;
		}

		if(!isFalse(l)){
			continue;
		}

		loopf.push_back(l);
		seen.getElem(var(l)) = isPositive(l) ? 2 : 1;
	}
}

/**
 * The given head is not false. So it has a (possibly looping) justification. Find this justification
 */
void IDSolver::findJustificationAggr(Var head, vec<Lit>& outjstf) {
	vec<Var> nonjstf;
	InterMediateDataStruct* currentjust = new InterMediateDataStruct(0,0); //create an empty justification
	const IDAgg& agg = *getAggDefiningHead(head);
	canJustifyHead(agg, outjstf, nonjstf, *currentjust, true);
	delete currentjust;
}

/**
 * Check whether the given var is justified by the current justification graph. If this is the case, jstf will
 * contain its justification and true will be returned. Otherwise, false will be returned and nonjstf will contain
 * all body literals of v that are not justified.
 */
bool IDSolver::directlyJustifiable(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, InterMediateDataStruct& currentjust) {
	const IDAgg& agg = *getAggDefiningHead(v);
	return canJustifyHead(agg, jstf, nonjstf, currentjust, false);
}

bool IDSolver::isInitiallyJustified(const IDAgg& agg){
	if(agg.getSign()==AGGSIGN_LB && getProp(agg.getType())->getMinPossible(agg.getWL())>=agg.getBound()){
		return true;
	}else if(agg.getSign()==AGGSIGN_UB && getProp(agg.getType())->getMaxPossible(agg.getWL())<=agg.getBound()){
		return true;
	}
	return false;
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
//	DefType type = type(v);
//
//	if(type==AGGR){return OLDCHECK;}
//	assert(type==CONJ || type==DISJ);
//
//	CCC c = definition[v];
//	//PropRule* c = definition[v];
//
//	for(int i=0; i<c->size(); ++i){
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
//	for(int i=0; i<c->size(); ++i){
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
//				for(int i=0; i<c->size(); ++i){
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
