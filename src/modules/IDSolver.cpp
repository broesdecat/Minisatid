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

// TODO in fact, having a propagator per scc might seem more logical?
// FIXME an unwellfounded model does NOT mean that the definition is not total
// TODO only add one loopform at a time (save all lits, check next time first whether all are false, otherwise choose one more)

// FIXME, when finishparsing returns present=false, the IDSolver should be deleted. Currenlty it still exists and addrule can still be called
// (and isinitialized is still false because finishparsing was aborted)

using namespace std;
using namespace MinisatID;

IDAgg::IDAgg(const Lit& head, AggBound b, AggSem sem, AggType type, const std::vector<WL>& origwls):
	bound(b), head(head), sem(sem), index(-1), type(type), wls(origwls){
	std::sort(wls.begin(), wls.end(), compareByWeights<WL>);
}

IDSolver::IDSolver(PCSolver* s, int definitionID):
		Propagator(s),
		definitionID(definitionID),
		minvar(0), nbvars(0),
		conj(DefType::CONJ), disj(DefType::DISJ), aggr(DefType::AGGR),
		sem(getPCSolver().modes().defsem),
		posrecagg(false), mixedrecagg(false),
		posloops(true), negloops(true),
		backtracked(true),
		adaption_total(0), adaption_current(0)
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
	for (auto i = css.cbegin(); i < css.cend(); ++i){
		isCS(*i) = false;
	}
	css.clear();
}

void IDSolver::adaptStructsToHead(Var head){
	nbvars = nVars();
	definitions.resize(nbvars, NULL);
}

/**
 * First literal in ps is the head of the rule. It has to be present and it has to be positive.
 *
 * if no body literals: empty set conjunction is TRUE, empty set disjunction is FALSE!
 *
 * If DefType::CONJ, then all body literals are inverted to create the completion clause
 * else, the head atom is inverted for the completion
 *
 * If only one body literal, the clause is always made conjunctive (for algorithmic correctness later on), semantics are the same.
 */
SATVAL IDSolver::addRule(bool conj, Var head, const litlist& ps) {
	if(getPCSolver().getCurrentDecisionLevel()!=0){
		getPCSolver().backtrackTo(0);
	}

	adaptStructsToHead(head);

	if(isDefined(head)){
		char s[100]; sprintf(s, "Multiple rules have the same head %d, which is not allowed!\n", getPrintableVar(head));
		throw idpexception(s);
	}

	if (ps.empty()) {
		Lit h = conj ? mkLit(head) : mkLit(head, true); //empty set conj = true, empty set disj = false
		InnerDisjunction v;
		v.literals.push_back(h);
		getPCSolver().add(v);
	} else {
		conj = conj || ps.size() == 1; //rules with only one body atom are treated as conjunctive

		auto r = new PropRule(mkLit(head), ps);
		createDefinition(head, r, conj?DefType::CONJ:DefType::DISJ);

		InnerEquivalence eq;
		eq.head = mkLit(head);
		eq.literals = ps;
		eq.conjunctive = conj;
		getPCSolver().add(eq);
		assert(isDefined(head));
	}

	if(getPCSolver().isInitialized() && modes().lazy){
		bool present = false;
		bool unsat = false;
		finishParsing(present, unsat);
	}

	return getPCSolver().satState();
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

void IDSolver::generateSCCs(){
	// Initialize scc of full dependency graph
	//TODO remove nVars!
	vector<bool> incomp(nVars(), false);
	varlist stack;
	vector<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	varlist mixedroots;
	sccroots.clear();
	varlist nodeinmixed;
	int counter = 1;

	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		if (visited[(*i)] == 0) {
			visitFull((*i), incomp, stack, visited, counter, true, sccroots, mixedroots, nodeinmixed);
		}
	}

	if (mixedroots.size() == 0) {
		negloops = false;
	}

	//all var in rootofmixed are the roots of mixed loops. All other are no loops (size 1) or positive loops

	// Initialize scc of positive dependency graph
	for (auto i=nodeinmixed.cbegin(); i!=nodeinmixed.cend(); ++i) {
		incomp[*i] = false;
		occ(*i) = MIXEDLOOP;
		visited[*i] = 0;
	}
	stack.clear();
	counter = 1;

	for (auto i=nodeinmixed.cbegin(); i!=nodeinmixed.cend(); ++i) {
		if (visited[*i] == 0) {
			visit(*i, incomp, stack, visited, counter, sccroots);
		}
	}

	if (verbosity() > 20) {
		report("Printing mapping from variables to the ID of the SCC in which it occurs:\n");
		for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
			report("SCC of %d is %d, ", getPrintableVar(*i), getPrintableVar(scc(*i)));
		}
		report("Ended printing sccs.\n");
	}
}

bool IDSolver::loopPossibleOver(Var v){
	DefType t = type(v);
	switch (t) {
		case DefType::DISJ:
		case DefType::CONJ:
			for (auto j = definition(v)->cbegin(); j < definition(v)->cend(); ++j) {
				Lit l = *j;
				if (inSameSCC(v, var(l))) {
					return true;
				}
			}
			break;
		case DefType::AGGR: {
			for (auto j = getSetLitsOfAggWithHeadBegin(v); j< getSetLitsOfAggWithHeadEnd(v); ++j) {
				if (inSameSCC(v, var((*j).getLit()))) { // NOTE: disregard sign here: set literals can occur both pos and neg in justifications.
					return true;
				}
			}
			break;
		}
	}
	return false;
}

void IDSolver::addToNetwork(Var v){
	//IMPORTANT: also add mixed loop rules to the network for checking well-founded model
	//could be moved to different datastructure to speed up
	switch(type(v)){
	case DefType::DISJ:
		for (auto j = definition(v)->cbegin(); j < definition(v)->cend(); ++j) {
			Lit l = *j;
			if(l==definition(v)->getHead()){
				continue;
			}
			disj.add(l, v);
		}
		break;
	case DefType::CONJ:
		for (auto j = definition(v)->cbegin(); j < definition(v)->cend(); ++j) {
			Lit l = *j;
			if(l==definition(v)->getHead()){
				continue;
			}
			conj.add(l, v);
		}
		break;
	case DefType::AGGR:
		for (auto j=(*aggdefinition(v)).getWL().cbegin(); j!=(*aggdefinition(v)).getWL().cend(); ++j) {
			aggr.add((*j).getLit(), v);
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
		case NONDEFOCC:
			assert(false);
			break;
		}
		break;
	}
}

/*
 * @PRE: aggregates have to have been finished
 */
void IDSolver::finishParsing(bool& present, bool& unsat) {
	notifyParsed();

	present = true;
	unsat = false;

	//LAZY initialization
	posloops = true; negloops = true; mixedrecagg = false; posrecagg = false;
	_seen = new InterMediateDataStruct(nbvars, minvar);
	disj.resize(nVars()*2);
	conj.resize(nVars()*2);
	aggr.resize(nVars()*2);

	if(modes().defsem==DEF_COMP || defdVars.size()==0){
		if(not modes().lazy){
			present = false;
		}
#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif
		return;
	}

	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) {
		assert(isDefined(*i));
		occ(*i)=NONDEFOCC;
	}

	if (verbosity() >= 1) {
		report("> Number of rules : %6zu.\n",defdVars.size());
	}

	// Determine which literals should no longer be considered defined (according to the scc in the positive graph) + init occurs
	int atoms_in_pos_loops = 0;
	varlist reducedVars;
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Var v = (*i);

		bool addtonetwork = false;
		if (loopPossibleOver(v)) { //might be in pos loop
			++atoms_in_pos_loops;
			occ(v) = occ(v) == MIXEDLOOP ? BOTHLOOP : POSLOOP;
			addtonetwork = true;
		} else { //can never be in posloop
			if (occ(v) == NONDEFOCC) { //will not occur in a loop
				//cerr <<getPrintableVar(v) <<" cannot be in any loop.\n";
				removeDefinition(v);
			} else if (occ(v) == MIXEDLOOP) { //might occur in a mixed loop
				//cerr <<getPrintableVar(v) <<" can be in a mixed loop.\n";
				addtonetwork = true;
			}
		}

		if(addtonetwork){
			reducedVars.push_back(v);
			addToNetwork(v);
		}
	}
	if(not modes().lazy){
		defdVars.clear();
		defdVars.insert(defdVars.begin(), reducedVars.cbegin(), reducedVars.cend());
	}

	if (atoms_in_pos_loops == 0) {
		posloops = false;
	}

	if(getSemantics()==DEF_STABLE){
		negloops = false;
	}

	if (!posloops && !negloops) {
		if(not modes().lazy){
			present = false;
		}
	}

	if (verbosity() >= 1) {
		report("> Number of recursive atoms in positive loops : %6d.\n",(int)atoms_in_pos_loops);
		if (negloops) {
			report("> Mixed loops also exist.\n");
		}
	}

	if(modes().bumpidonstart){
		bumpHeadHeuristic();
	}

	unsat = not simplifyGraph(atoms_in_pos_loops);

	if(not unsat && modes().tocnf){
		unsat = transformToCNF(sccroots, present)==SATVAL::UNSAT;
	}

	notifyInitialized();

	if(unsat){
		getPCSolver().notifyUnsat();
	}else{
#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif
	}
}

void IDSolver::bumpHeadHeuristic(){
	//This heuristic on its own solves hamiltonian path for slow decay
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		const Var& v = *i;
		if(isDefined(v) && type(v)==DefType::DISJ){
			const PropRule& r = *definition(v);
			for(vsize j=0; j<r.size(); ++j){
				getPCSolver().varBumpActivity(var(r[j]));
			}
		}
	}
}

SATVAL IDSolver::transformToCNF(const varlist& sccroots, bool& present){
	vector<toCNF::Rule*> rules;
	bool unsat = false;
	for(auto root = sccroots.cbegin(); root!=sccroots.cend(); ++root){
		// TODO better to store full sccs instead having to loop over them here?
		for(auto i=defdVars.cbegin(); i<defdVars.cend(); ++i){
			if(scc(*root)==scc(*i)){
				litlist defbodylits;
				litlist openbodylits;
				auto proprule = getDefVar(*i)->definition();
				for(auto bodylit=proprule->cbegin(); bodylit!=proprule->cend(); ++bodylit){
					if(not sign(*bodylit) && hasDefVar(var(*bodylit)) && scc(var(*bodylit))==scc(*root)){
						defbodylits.push_back(*bodylit);
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
	if(not negloops && not modes().lazy){
		present = false;
	}
	return unsat?SATVAL::UNSAT:SATVAL::POS_SAT;
}

void IDSolver::removeDefinition(Var head) {
	if(modes().lazy){
		return;
	}
	delete getDefVar(head); setDefVar(head, NULL);
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the FULL dependency graph
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visitFull(Var i, vector<bool> &incomp, varlist &stack, varlist &visited,
		int& counter, bool throughPositiveLit, varlist& posroots, varlist& rootofmixed, varlist& nodeinmixed) {
	assert(!incomp[i]);
	assert(isDefined(i));
	++counter;
	visited[i] = throughPositiveLit ? counter : -counter;
	scc(i) = i;
	stack.push_back(i);

	switch (type(i)) {
		case DefType::DISJ:
		case DefType::CONJ: {
			PropRule const * const r = definition(i);
			for (vsize j = 0; j < r->size(); ++j) {
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
		case DefType::AGGR: {
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
		varlist sccs;
		bool mixed = false;
		int w;
		posroots.push_back(i);
		do {
			w = stack.back();
			stack.pop_back();
			visited[w] < 0 ? mixed = true : true;
			scc(w) = i; //these are the found sccs
			sccs.push_back(w);
			incomp[w] = true;
		} while (w != i);
		if (mixed && sccs.size()>1) {
			rootofmixed.push_back(i);
			nodeinmixed.insert(nodeinmixed.begin(), sccs.cbegin(), sccs.cend());
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
void IDSolver::visit(Var i, vector<bool> &incomp, varlist &stack, varlist &visited, int& counter, varlist& roots) {
	assert(scc(i)>=0 && scc(i)<nbvars);
	assert(!incomp[i]);
	visited[i] = ++counter;
	scc(i) = i;
	stack.push_back(i);

	switch (type(i)) {
		case DefType::DISJ:
		case DefType::CONJ: {
			PropRule const * const r = definition(i);
			for (vsize j = 0; j < r->size(); ++j) {
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
		case DefType::AGGR: {
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
	}

	if (scc(i) == i) {
		int w;
		roots.push_back(i);
		do {
			w = stack.back();
			stack.pop_back();
			scc(w) = i; //these are the found sccs
			incomp[w] = true;
		} while (w != i);
	}
}

// NOTE: essentially, simplifygraph can be called anytime the level-0 interpretation has changed.
// In default model expansion, this turned out to be quite expensive, so it was disabled.
bool IDSolver::simplifyGraph(int atomsinposloops){
	if(!posloops){
		return true;
	}

	for(auto i=defdVars.cbegin(); i<defdVars.cend(); ++i){
		justification(*i).clear();
	}

	varlist usedseen; //stores which elements in the "seen" datastructure we adapted to reset them later on
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Var v = (*i);
		if (isFalse(v)) {
			continue;
		}
		switch (type(v)) {
			case DefType::DISJ:
			case DefType::AGGR:
				seen(v) = 1;
				break;
			case DefType::CONJ:
				seen(v) = definition(v)->size();
				break;
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

		litlist heads;
		vector<litlist > jstf;

		propagateJustificationDisj(l, jstf, heads);
		for (vsize i = 0; i < heads.size(); ++i) {
			assert(jstf[i].size()>0);
			changejust(var(heads[i]), jstf[i]);
			propq.push(heads[i]);
		}
		heads.clear();
		jstf.clear();

		propagateJustificationAggr(l, jstf, heads);
		for (vsize i = 0; i < heads.size(); ++i) {
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
	varlist reducedVars;
	posrecagg = false;
	mixedrecagg = false;
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Var v = (*i);
		if (seen(v) > 0 || isFalse(v)) {
			if (verbosity() >= 2) {
				report(" %d", getPrintableVar(v));
			}
			if(isTrue(v)){
				return false;
			}
			if(isUnknown(v)) {
				getPCSolver().setTrue(createNegativeLiteral(v), this);
			}

			if (occ(v) == POSLOOP) {
				//FIXME lazy grounding removeDefinition(v);
				--atomsinposloops;
			} else {
				occ(v) = MIXEDLOOP;
				reducedVars.push_back(v);
				if (type(v) == DefType::AGGR) {
					mixedrecagg = true;
				}
			}
		} else {
			reducedVars.push_back(v);
			if(type(v)==DefType::AGGR){
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
	defdVars.insert(defdVars.begin(), reducedVars.cbegin(), reducedVars.cend());

	//reconstruct the disj and conj occurs with the reduced number of definitions
	disj.clear();
	conj.clear();
	disj.resize(2*nVars());
	conj.resize(2*nVars());
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Var v = (*i);
		if (type(v) == DefType::CONJ || type(v) == DefType::DISJ) {
			const PropRule& dfn = *definition(v);
			for (auto litit=dfn.cbegin(); litit!=dfn.cend(); ++litit) {
				if (*litit != dfn.getHead()) { //don't look for a justification that is the head literal itself
					if (type(v) == DefType::DISJ) {
						disj.add(*litit, v);
					} else if (type(v) == DefType::CONJ) {
						conj.add(*litit, v);
					}
				}
			}
		}else{
			const IDAgg& dfn = *aggdefinition(v);
			for (auto j=dfn.getWL().cbegin(); j!=dfn.getWL().cend(); ++j) {
				aggr.add((*j).getLit(), v);
			}
		}
	}

	//Reset the elements in "seen" that were changed
	//NOTE: do not return before this call!
	for (auto i = usedseen.cbegin(); i < usedseen.cend(); ++i) {
		seen(*i) = 0;
	}

	if (verbosity() >= 2) {
		report(" ]\n");
	}

	if (atomsinposloops == 0) {
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
	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Var var = *i;
		assert(hasDefVar(var));
		//assert(justification(var).size()>0 || type(var)!=DefType::DISJ || occ(var)==MIXEDLOOP); FIXME lazy grounding hack (because invar that def gets deleted)

		if(verbosity()>=9){
			clog <<getPrintableVar(var) <<"<-";
			bool begin = true;
			count++;
			for(auto i=justification(var).cbegin(); i!=justification(var).cend(); ++i){
				if(!begin){
					clog <<",";
				}
				begin = false;
				clog <<*i;
			}
			clog <<";";
			if(count%30==0){
				clog <<"\n";
			}
		}

		Lit l(createPositiveLiteral(var));
		for (auto j = disj.occurs(l).cbegin(); j < disj.occurs(l).cend(); ++j) {
			assert(type(*j)==DefType::DISJ);
		}
		for (auto j = conj.occurs(l).cbegin(); j < conj.occurs(l).cend(); ++j) {
			assert(type(*j)==DefType::CONJ);
		}
		l = createNegativeLiteral(var);
		for (auto j = disj.occurs(l).cbegin(); j < disj.occurs(l).cend(); ++j) {
			assert(type(*j)==DefType::DISJ);
		}
		for (auto j = conj.occurs(l).cbegin(); j < conj.occurs(l).cend(); ++j) {
			assert(type(*j)==DefType::CONJ);
		}
	}
	if(verbosity()>=9){
		clog <<"\n";
	}
#endif

#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
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
void IDSolver::propagateJustificationDisj(const Lit& l, vector<litlist>& jstf, litlist& heads) {
	const varlist& dd = disj.occurs(l);
	for (auto i = dd.cbegin(); i < dd.cend(); ++i) {
		const Var& v = *i;
		if (isFalse(v) || seen(v) == 0) {
			continue;
		}
		seen(v) = 0;
		heads.push_back(createPositiveLiteral(v));
		jstf.push_back(litlist{l});
	}
}

void IDSolver::propagateJustificationConj(const Lit& l, std::queue<Lit>& heads) {
	const varlist& ll = conj.occurs(l);
	for (auto i = ll.cbegin(); i < ll.cend(); ++i) {
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

void IDSolver::propagateJustificationConj(const Lit& l, litlist& heads) {
	const varlist& ll = conj.occurs(l);
	for (auto i = ll.cbegin(); i < ll.cend(); ++i) {
		const Var& v = *i;
		if (isFalse(v) || seen(v) == 0) {
			continue;
		}
		seen(v)--;
		if (seen(v) == 0) {
			heads.push_back(createPositiveLiteral(v));
		}
	}
}

void IDSolver::propagateJustificationAggr(const Lit& l, vector<litlist >& jstfs, litlist& heads) {
	for(auto i = aggr.occurs(l).cbegin(); i < aggr.occurs(l).cend(); ++i) {
		const IDAgg& agg = *aggdefinition(*i);
		if (isFalse(agg.getHead())) {
			continue;
		}

		Var head = var(agg.getHead());
		if (seen(head) > 0) { //only check its body for justification when it has not yet been derived
			litlist jstf;
			varlist nonjstf;

			if (canJustifyHead(agg, jstf, nonjstf, *_seen, false)) {
				seen(head) = 0;
				heads.push_back(mkLit(head, false));
				jstfs.push_back(jstf);
			}
		}
	}
}

/*
 * IMPORTANT: should ONLY be called after all possible other propagations have been done:
 * the state has to be stable for both aggregate and unit propagations
 */
rClause IDSolver::notifypropagate() {
#ifdef DEBUG
	assert(getPCSolver().satState()!=SATVAL::UNSAT);
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif

	// There was an unfounded set saved which might not have been completely propagated by unit propagation
	// So check if there are any literals unknown and add more loopformulas
	if(savedufs.size()!=0){
		for(auto i=savedufs.cbegin(); i!=savedufs.cend(); ++i){
			if(!isFalse(*i)){
				Lit l = createNegativeLiteral(*i);
				addLoopfClause(l, savedloopf);
#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif
				return nullPtrClause;
			}
		}
		savedufs.clear(); //none found
	}

	if(not posloops || not isInitialized() || not indirectPropagateNow()){
#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif
		return nullPtrClause;
	}

	findCycleSources();

	if (css.empty()) {
#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif
		return nullPtrClause;
	}

	uint64_t old_justify_calls = stats.justify_calls;

	std::set<Var> ufs;
	bool ufs_found = false;
	for (auto j = css.cbegin(); !ufs_found && j < css.cend(); ++j) {
		if (isCS(*j)) {
			ufs_found = unfounded(*j, ufs);
		}
	}

	// stats.justifiable_cycle_sources += ufs_found ? (j - 1) : j; // This includes those that are removed inside "unfounded".
	stats.succesful_justify_calls += (stats.justify_calls - old_justify_calls);

	rClause confl = nullPtrClause;
	if (ufs_found) {
		if (verbosity() >= 2) {
			report("Found an unfounded set of size %d: {",(int)ufs.size());
			for (std::set<Var>::const_iterator it = ufs.cbegin(); it != ufs.cend(); ++it) {
				report(" %d",getPrintableVar(*it));
			}
			report(" }.\n");
		}
		++stats.cycles;
		stats.cycle_sizes += ufs.size();
		if (getPCSolver().modes().defn_strategy == adaptive) {
			++adaption_current; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
		}
		confl = assertUnfoundedSet(ufs);
	} else { // Found a witness justification.
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

#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif

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
			const varlist& ds = disj.occurs(not l);
			for (auto j = ds.cbegin(); j < ds.cend(); ++j) {
				checkJustification(*j);
			}

			varlist heads = getDefAggHeadsWithBodyLit(var(not l));
			for (auto j = heads.cbegin(); j < heads.cend(); ++j) {
				if(hasDefVar(*j)){
					checkJustification(*j);
				}
			}
		}
	} else { //Only if not always and backtracked
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		backtracked = false;
		for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
			if (type(*i) == DefType::DISJ || type(*i) == DefType::AGGR) {
				checkJustification(*i);
			}
		}
	}
	if (verbosity() >= 2) {
		report("Indirect propagations. Verifying %zu cycle sources:",css.size());
		for (auto i = css.cbegin(); i < css.cend(); ++i) {
			report(" %d", getPrintableVar(*i));
		}
		report(".\n");
	}
	++stats.nb_times_findCS;
	stats.cycle_sources += css.size();
}

void IDSolver::checkJustification(Var head) {
	if (!isDefInPosGraph(head) || isFalse(head) || isCS(head)) {
		return;
	}

	bool justfalse = false;
	for (vsize i = 0; !justfalse && i < justification(head).size(); ++i) {
		if (isFalse(justification(head)[i])) {
			justfalse = true;
		}
	}
	if (!justfalse) {
		return;
	}

	//Incorrect to prune out heads in which Lit is not the justification

	//Possible heuristic: getPCSolver().varBumpActivity(head);

	litlist jstf;
	bool external = true;

	if (type(head) == DefType::DISJ) {
		findJustificationDisj(head, jstf);
	} else {
		assert(type(head)==DefType::AGGR);
		findJustificationAggr(head, jstf);
	}
	for (vsize i = 0; external && i < jstf.size(); ++i) {
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
void IDSolver::findJustificationDisj(Var v, litlist& jstf) {
	const PropRule& c = *definition(v);
	int pos = -1;
	for (vsize i = 0; i < c.size(); ++i) {
		if (!isFalse(c[i])) {
			pos = i;
			if (!inSameSCC(v, var(c[i])) || !isPositive(c[i]) || !isDefined(var(c[i]))) {
				break; //external justification is preferred.
			}
		}
	}
	assert(pos>=0);
	jstf.push_back(c[pos]);
}

/*
 * Return true if indirectpropagation is necessary. This is certainly necessary if the state is two-valued or if the strategy is always.
 */
bool IDSolver::indirectPropagateNow() {
	bool propagate = true;
	// if not always and state is three-valued.
	if (getPCSolver().modes().defn_strategy != always && !getPCSolver().hasTotalModel()) {
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
	++stats.justify_calls;
	varlist tmpseen; // use to speed up the cleaning of data structures in "Finish"
	queue<Var> q;
	Var v;

#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
		assert(seen(*i)==0);
	}
#endif

	markNonJustified(cs, tmpseen);
	bool csisjustified = false;

	seen(cs) = 1; //no valid justification can be created just from looking at the body literals
	tmpseen.push_back(cs);

	if (verbosity() > 9) {
		for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
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

	for (vsize i = 0; i < tmpseen.size(); ++i) {
		seen(tmpseen[i]) = 0;
	}

#ifdef DEBUG
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should have been erased
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
bool IDSolver::findJustificationDisj(Var v, litlist& jstf, varlist& nonjstf) {
	const PropRule& c = *definition(v);
	bool externallyjustified = false;
	seen(v) = 1;
	int pos = -1;
	for (vsize i = 0; !externallyjustified && i < c.size(); ++i) {
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
				nonjstf.push_back(var(c[i]));
			}
		}
	}
	if (pos >= 0) {
		jstf.push_back(c[pos]);
		seen(v) = 0;
	}
	return seen(v) == 0;
}

bool IDSolver::findJustificationConj(Var v, litlist& jstf, varlist& nonjstf) {
	const PropRule& c = *definition(v);
	seen(v) = 0;
	for (vsize i = 0; i < c.size(); ++i) {
		if (isPositive(c[i]) && seen(var(c[i])) != 0) {
			++seen(v);
			nonjstf.push_back(var(c[i]));
		}
	}
	return seen(v) == 0;
}

bool IDSolver::findJustificationAggr(Var v, litlist& jstf, varlist& nonjstf) {
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
	litlist jstf;
	varlist nonjstf;
	bool justified;

	switch (type(v)) {
		case DefType::CONJ:
			justified = findJustificationConj(v, jstf, nonjstf);
			break;
		case DefType::DISJ:
			justified = findJustificationDisj(v, jstf, nonjstf);
			break;
		case DefType::AGGR:
			justified = findJustificationAggr(v, jstf, nonjstf);
			break;
		default:
			assert(false);
			throw idpexception("The program tried to justify a rule that was not DefType::AGGR, DefType::DISJ or DefType::CONJ.\n");
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
		for (vsize i = 0; i < nonjstf.size(); ++i) {
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
	varlist justifiedq;
	justifiedq.push_back(v); // literals that have to be justified
	while (justifiedq.size() > 0) {
		Var k = justifiedq.back();
		justifiedq.pop_back();

		// Make it justified.
		ufs.erase(k);

		isCS(k) = false;
		++stats.cs_removed_in_justify;

		if (k == cs) {
			return true;
		}

		Lit bdl = createPositiveLiteral(k);

		litlist heads;
		vector<litlist > jstf;
		propagateJustificationDisj(bdl, jstf, heads);
		propagateJustificationAggr(bdl, jstf, heads);

		for (vsize i = 0; i < heads.size(); ++i) {
			assert(jstf[i].size()>0);
			changejust(var(heads[i]), jstf[i]);
			justifiedq.push_back(var(heads[i]));
			if (verbosity() > 5) {
				report("justified %d\n", getPrintableVar(var(heads[i])));
			}
		}

		heads.clear();
		propagateJustificationConj(bdl, heads);
		for (int i = 0; i < heads.size(); ++i) {
			justifiedq.push_back(var(heads[i]));
			if (verbosity() > 5) {
				report("justified %d\n", getPrintableVar(var(heads[i])));
			}
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void IDSolver::changejust(Var v, litlist& just) {
	assert(just.size()>0 || type(v)==DefType::AGGR); //justification can be empty for aggregates
	justification(v) = just;
	for(vsize i=0; i<just.size(); ++i){
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
	for (auto i=defdVars.cbegin(); i!=defdVars.cend(); ++i) { //seen should be cleared
		assert(seen(*i)==0);
	}
#endif

	//In seen, we store literals that have been added to the loopf or found not to belong in it.
	//seen(A)==1 indicates that A has been added
	//seen(A)==2 indicates that not A has been added
	//Both can be added once, because of the assumption that a rule has been simplified to only contain any of them once

	for (std::set<Var>::const_iterator tch = ufs.cbegin(); tch != ufs.cend(); ++tch) {
		switch (type(*tch)) {
			case DefType::CONJ: //
				break;
			case DefType::DISJ: {
				const PropRule& c = *definition(*tch);
				for (vsize i = 0; i < c.size(); ++i) {
					Lit l = c[i];
					if ((!isDefined(var(l)) || seen(var(l))!=(isPositive(l)?2:1)) && ufs.find(var(c[i])) == ufs.cend()) {
						assert(isFalse(l));
						loopf.push_back(l);
						seen(var(l)) = (isPositive(l) ? 2 : 1);
					}
				}
				break;
			}
			case DefType::AGGR:
				addExternalLiterals(*tch, ufs, loopf, *_seen);
				break;
			default:
				assert(false);
				throw idpexception("Only DefType::AGGR, DefType::CONJ or DefType::DISJ should be checked for external disjuncts!\n");
				break;
		}
	}

	for (vsize i = 1; i < loopf.size(); ++i) {
		seen(var(loopf[i])) = 0;
	}
	stats.extdisj_sizes += loopf.size() - 1;
}

/**
 * If an atom of 'ufs' was already true, return a loop formula for this (one such) atom as conflicting clause.
 * Otherwise, add a loop formula for each atom in ufs, enqueue the negation of
 * each of those atoms, and return NULL.
 * For each atom in UFS that is false, don't do anything
 *
 * Loop formulas are created in the form
 * UFSLITERAL IMPLIES DefType::DISJUNCTION(external disjuncts)
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
	for (std::set<Var>::iterator tch = ufs.cbegin(); tch != ufs.cend(); ++tch) {
		if (isTrue(*tch)) {
			loopf.literals[0] = createNegativeLiteral(*tch); //negate the head to create a clause
			rClause c = getPCSolver().createClause(loopf, true);
			getPCSolver().addLearnedClause(c);
			++stats.justify_conflicts;
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
		Lit l = createNegativeLiteral(*ufs.cbegin());
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

		for (std::set<Var>::iterator tch = ufs.cbegin(); tch != ufs.cend(); ++tch) {
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
void IDSolver::markNonJustified(Var cs, varlist& tmpseen) {
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

void IDSolver::markNonJustifiedAddParents(Var x, Var cs, queue<Var> &q, varlist& tmpseen) {
	Lit poslit = createPositiveLiteral(x);
	const varlist& v = disj.occurs(poslit);
	for (auto i = v.cbegin(); i < v.cend(); ++i) {
		if (isDefInPosGraph(*i) && var(justification(*i)[0]) == x) {
			markNonJustifiedAddVar(*i, cs, q, tmpseen);
		}
	}
	const varlist& w = conj.occurs(poslit);
	for (auto i = w.cbegin(); i < w.cend(); ++i) {
		markNonJustifiedAddVar(*i, cs, q, tmpseen);
	}
	varlist heads = getDefAggHeadsWithBodyLit(x);
	for (varlist::size_type i = 0; i < heads.size(); ++i) {
		litlist& jstfc = justification(heads[i]);
		for (vsize k = 0; k < jstfc.size(); ++k) {
			if (jstfc[k] == poslit) { // Found that x is actually used in y's justification.
				markNonJustifiedAddVar(heads[i], cs, q, tmpseen);
				break;
			}
		}
	}
}

inline void IDSolver::markNonJustifiedAddVar(Var v, Var cs, queue<Var> &q, varlist& tmpseen) {
	// TODO prove whether this false can be here?
	if (/*!isFalse(v) && */ inSameSCC(v, cs) && (getPCSolver().modes().defn_search == include_cs || v == cs || !isCS(v))) {
		if (seen(v) == 0) {
			seen(v) = 1;
			tmpseen.push_back(v);
			q.push(v);
			++stats.total_marked_size;
		} else {
			++seen(v);
		}

		if (verbosity() > 9) {
			report("Not justified %d, times %d\n", getPrintableVar(v), seen(v));
		}
	}
}

inline void IDSolver::print(const PropRule& c) const {
	report("Rule ");
	Lit head = c.getHead();
	MinisatID::print(head, value(head));
	report(" <- ");
	for (vsize i = 0; i < c.size(); ++i) {
		MinisatID::print(c[i], value(c[i]));
		fprintf(stderr, " ");
	}
	report("\n");
}

/**
 * Checks if there are any positive loops in the current dependecy graph. Mainly used for debugging purposes (does slow bottom-up reasoning)
 */
bool IDSolver::isCycleFree() const {
	if(!modes().checkcyclefreeness){
		return true;
	}
#ifdef DEBUG
	for (int i = 0; i < nbvars; ++i) {
		assert(!isDefined(i) || justification(i).size()>0 || type(i)!=DefType::DISJ || occ(i)==MIXEDLOOP);
	}
#endif

	if (verbosity() >= 2) {
		report("Showing justification for disjunctive atoms. <<<<<<<<<<\n");
		for (int i = 0; i < nbvars; ++i) {
			if (isDefined(i) && type(i) == DefType::DISJ && occ(i) != MIXEDLOOP) {
				clog <<mkLit(i, false) <<"<-" <<justification(i)[0] <<"; ";
			}
		}
		report(">>>>>>>>>>\n");
	}

	// Verify cycles.
	varlist isfree(nbvars, 0); // per variable. 0 = free, >0 = number of literals in body still to be justified.
	litlist justified;
	uint cnt_nonjustified = 0;
	for (int i = 0; i < nbvars; ++i) {
		justified.push_back(mkLit(i, true)); // negative literals are justified anyhow.
		if (!isDefInPosGraph(i)) {
			justified.push_back(mkLit(i, false));
		} else {
			++cnt_nonjustified;
			isfree[i] = type(i) == DefType::CONJ ? definition(i)->size() : 1;

			if (type(i) == DefType::DISJ) {
				if (value(i) == l_True) {
					assert(value(justification(i)[0])!=l_False);
				} else {
					for (vsize j = 0; j < definition(i)->size(); ++j) {
						assert(value(definition(i)->operator [](j))!=l_True);
					}
				}
			} else {
				if (value(i) == l_True) {
					for (vsize j = 0; j < definition(i)->size(); ++j) {
						assert(value(definition(i)->operator [](j))!=l_False);
					}
				} else {
					bool found = false;
					for (vsize j = 0; !found && j < definition(i)->size(); ++j) {
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

		if(nbvars <= toInt(l)){
			continue;
		}

		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			Var d = *i;
			assert(type(d)==DefType::DISJ && (!isDefInPosGraph(*i) || justification(d).size()==1));
			if (isfree[d] > 0 && justification(d)[0] == l) {
				assert(isfree[d]==1);
				isfree[d] = 0;
				justified.push_back(mkLit(d, false));
				--cnt_nonjustified;
			}
		}

		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			Var c = *i;
			assert(type(c)==DefType::CONJ);
			if (isfree[c] > 0) {
				isfree[c]--;
				if (isfree[c] == 0) {
					justified.push_back(mkLit(c, false));
					--cnt_nonjustified;
				}
			}
		}

		varlist as = getDefAggHeadsWithBodyLit(var(l));
		for (int i=0;i<as.size();++i) {
			Var d = as[i];
			bool found = false;
			for(int j=0; j<justification(d).size(); ++j){
				if (justification(d)[j]==l && isfree[d]>0) {
					found = true;
					break;
				}
			}
			if(found){
				isfree[d]--;
				if (isfree[d]==0) {
					justified.push_back(mkLit(d,false));
					--cnt_nonjustified;
				}
			}
		}
	}

	if(cnt_nonjustified==0){
		if (verbosity() > 2) {
			clog <<"OK, the justification is cycle free.\n";
		}
	}else{
		if (verbosity() > 2) {
			clog <<"WARNING: " <<cnt_nonjustified <<" literals remain not-justified.\n";
		}
	}
	return cnt_nonjustified==0;
}

rClause IDSolver::notifyFullAssignmentFound(){
	rClause confl = nullPtrClause;
	if(confl==nullPtrClause){ // FIXME should separate propagators!
		notifypropagate();
	}
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
bool printednontotalwarning = false;

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
	varlist rootofmixed;
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

	if(verbosity()>0 && not printednontotalwarning){
		printednontotalwarning = true;
		report("The definition is not total (found an interpretation of the open symbols with a three-valued well-founded model).\n");
	}
	if (verbosity() > 1) {
		report("The model is not well-founded!\n");
	}

	//Returns the found assignment (TODO might be optimized to just return the loop)
	const litlist& decisions = getPCSolver().getDecisions();
	InnerDisjunction invalidation;
	for(auto i=decisions.cbegin(); i<decisions.cend(); ++i){
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
void IDSolver::findMixedCycles(varlist &root, vector<int>& rootofmixed) {
	vector<bool> incomp(nbvars, false);
	stack<Var> stack;
	vector<int> visited(nbvars, 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	int counter = 1;

	for (auto i = defdVars.cbegin(); i < defdVars.cend(); ++i) {
		Var v = *i;
		if (visited[v] == 0) {
			visitWF(v, root, incomp, stack, visited, counter, true, rootofmixed);
		}
	}
}

void IDSolver::visitWF(Var v, varlist &root, vector<bool> &incomp, stack<Var> &stack, varlist &visited,
		int& counter, bool throughPositiveLit, vector<int>& rootofmixed) {
	assert(!incomp[v]);
	assert(isDefined(v));
	++counter;
	visited[v] = throughPositiveLit ? counter : -counter;
	root[v] = v;
	stack.push(v);

	bool headtrue = value(v) == l_True;

	if (type(v) == DefType::AGGR) {
		/*litlist lits;
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
		for (vsize i = 0; i < definition(v)->size(); ++i) {
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
	} else {//head is true and DefType::DISJ or head is false and DefType::CONJ: one literal is needed for justification
		// for DefType::DISJ, the justification is already known TODO INCORRECT when no pos loops possible over head!
		// for a DefType::CONJ, randomly choose one of the false body literals. If there is no loop through it, then it is a good choice.
		//			If there is, it will be found later if another false literal exists without a mixed loop.
		Lit l = mkLit(-1);
		if (isConjunctive(v)) {
			for (vsize i = 0; i < definition(v)->size(); ++i) {
				Lit l2 = definition(v)->operator [](i);
				if (isFalse(l2)) {
					l = l2;
					break;
				}
			}
		} else {
			for (vsize i = 0; i < definition(v)->size(); ++i) {
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
	for (varlist::size_type n = 0; n < wfrootnodes.size(); ++n) {
		Var temp = wfrootnodes[n];
		mark(temp);
	}

	while (!wfqueue.empty()) {
		Lit l = wfqueue.front();
		wfqueue.pop();

		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			mark(*i);
		}
		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			mark(*i);
		}

		l = not l;

		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			mark(*i);
		}
		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			mark(*i);
		}


		/*TODO? if(aggsolver!=NULL){
		 litlist heads;
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
 * The DefType::CONJ counters count the number of literals still needed to make the DefType::CONJ true
 * The DefType::DISJ counters count the number of literals still needed to make the DefType::DISJ false
 */
void IDSolver::initializeCounters() {
	for (set<Var>::iterator i = wfmarkedAtoms.cbegin(); i != wfmarkedAtoms.cend(); ++i) {
		Var v = *i;
		seen(v) = 0;
		bool canbepropagated = false;
		for (vsize j = 0; !canbepropagated && j < definition(v)->size(); ++j) {
			Lit bl = definition(v)->operator [](j);
			if (wfisMarked[var(bl)]) {
				++seen(v);
			} else if (isFalse(bl) && type(v) == DefType::CONJ) {
				canbepropagated = true;
			} else if (isTrue(bl) && type(v) == DefType::DISJ && var(bl) != v) {
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
 * Counters probably keep the number of literals needed to make it true for DefType::CONJ and the number of literals needed to make it false for DefType::DISJ!!!
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
		//if DefType::DISJ, then head will be true, so add true head to queue and set counter to 0
		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			Var head = *i;
			if (wfisMarked[head]) {
				wfqueue.push(createPositiveLiteral(head));
				seen(head) = 0;
			}
		}

		//if DefType::CONJ and counter gets 0, then head will be true, so add true head to queue
		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			Var head = *i;
			if (wfisMarked[head] && --seen(head) == 0) {
				wfqueue.push(createPositiveLiteral(head));
			}
		}

		l = not l;

		//Literal l has become false, so for all rules with body literal l and marked head,
		//if DefType::DISJ and counter gets 0, then head will be false, so add false head to queue
		for (auto i = disj.occurs(l).cbegin(); i < disj.occurs(l).cend(); ++i) {
			Var head = *i;
			if (wfisMarked[head] && --seen(head) == 0) {
				wfqueue.push(createNegativeLiteral(head));
			}
		}

		//if DefType::CONJ, then head will be false, so add false head to queue and set counter to 0
		for (auto i = conj.occurs(l).cbegin(); i < conj.occurs(l).cend(); ++i) {
			Var head = *i;
			if (wfisMarked[head]) {
				wfqueue.push(createNegativeLiteral(head));
				seen(head) = 0;
			}
		}

		//TODO DefType::AGGREGATES
	}
}

/**
 * Overestimate the counters by making all negative defined marked body literals true.
 */
void IDSolver::overestimateCounters() {
	for (set<Var>::iterator i = wfmarkedAtoms.cbegin(); i != wfmarkedAtoms.cend(); ++i) {
		Var v = *i;
		assert(seen(v) > 0);

		for (vsize j = 0; j < definition(v)->size(); ++j) {
			const Lit& bdl = definition(v)->operator [](j);
			if (wfisMarked[var(bdl)] && !isPositive(bdl) && v != var(bdl)) {
				if (type(v) == DefType::CONJ) {
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
	for (set<Var>::iterator i = wfmarkedAtoms.cbegin(); i != wfmarkedAtoms.cend(); ++i) {
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

// PRINT INFORMATION

void IDSolver::printState() const{
	MinisatID::print(this);
}


void IDSolver::printStatistics() const {
	stats.print();
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

bool IDSolver::canJustifyHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	if(agg.getType()==MAX){
		return canJustifyMaxHead(agg, jstf, nonjstf, currentjust, real);
	}else{
		assert(agg.getType()==PROD || agg.getType()==SUM || agg.getType()==CARD);
		return canJustifySPHead(agg, jstf, nonjstf, currentjust, real);
	}
}

bool IDSolver::canJustifyMaxHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	bool justified = true;
	const vwl& wl = agg.getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		for (auto i = wl.crbegin(); i < wl.crend() && i->getWeight() > agg.getBound(); ++i) {
			if (oppositeIsJustified(currentjust, *i, real)) {
				jstf.push_back(not i->getLit()); //push negative literal, because it should become false
			} else if (real || currentjust.getElem(var(i->getLit())) != 0) {
				nonjstf.push_back(var(i->getLit()));
			}
		}
		if (nonjstf.size() == 0) {
			justified = true;
		}
	}

	if(justified && agg.hasLB()){
		justified = false;
		for (auto i = wl.crbegin(); i < wl.crend() && i->getWeight() >= agg.getBound(); ++i) {
			if (isJustified(currentjust, *i, real)) {
				jstf.push_back(i->getLit());
				justified = true;
			} else if (real || (currentjust.hasElem(var(i->getLit())) && currentjust.getElem(var(i->getLit())) != 0)) {
				nonjstf.push_back(var(i->getLit()));
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
bool IDSolver::canJustifySPHead(const IDAgg& agg, litlist& jstf, varlist& nonjstf, const InterMediateDataStruct& currentjust, bool real) const {
	const AggProp& type = *getProp(agg.getType());
	bool justified = true;
	const vwl& wl = agg.getWL();

	if (justified && agg.hasUB()) {
		justified = false;
		Weight bestpossible = type.getMaxPossible(wl);
		for (vwl::const_iterator i = wl.cbegin(); !justified && i < wl.cend(); ++i) {
			if (oppositeIsJustified(currentjust, *i, real)) {
				jstf.push_back(not i->getLit());
				bestpossible = type.removeMax(bestpossible, i->getWeight());
				if (bestpossible <= agg.getBound()) {
					justified = true;
				}
			} else if (real || currentjust.getElem(var(i->getLit())) != 0) {
				nonjstf.push_back(var(i->getLit()));
			}
		}
	}
	if(justified && agg.hasLB()){
		justified = false;
		Weight bestcertain = type.getMinPossible(wl);
		for (vwl::const_iterator i = wl.cbegin(); !justified && i < wl.cend(); ++i) {
			if (isJustified(currentjust, *i, real)) {
				jstf.push_back(i->getLit());
				bestcertain = type.add(bestcertain, i->getWeight());
				if (bestcertain >= agg.getBound()) {
					justified = true;
				}
			} else if (real || (currentjust.hasElem(var(i->getLit())) && currentjust.getElem(var(i->getLit())) != 0)) {
				nonjstf.push_back(var(i->getLit()));
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

varlist IDSolver::getDefAggHeadsWithBodyLit(Var x) const{
	varlist heads;
	for (auto i = aggr.occurs(mkLit(x)).cbegin(); i < aggr.occurs(mkLit(x)).cend(); ++i) {
		heads.push_back(var(aggdefinition(*i)->getHead()));
	}
	return heads;
}

vwl::const_iterator IDSolver::getSetLitsOfAggWithHeadBegin(Var x) const {
	return getAggDefiningHead(x)->getWL().cbegin();
}

vwl::const_iterator IDSolver::getSetLitsOfAggWithHeadEnd(Var x) const {
	return getAggDefiningHead(x)->getWL().cend();
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
	for (vwl::const_iterator i = getAggDefiningHead(v)->getWL().cbegin(); i < getAggDefiningHead(v)->getWL().cend(); ++i) {
		Lit l = i->getLit();
		if(ufs.find(var(l)) != ufs.cend() || seen.getElem(var(l)) == (isPositive(l) ? 2 : 1)){
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
void IDSolver::findJustificationAggr(Var head, litlist& outjstf) {
	varlist nonjstf;
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
bool IDSolver::directlyJustifiable(Var v, litlist& jstf, varlist& nonjstf, InterMediateDataStruct& currentjust) {
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
