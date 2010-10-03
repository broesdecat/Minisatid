//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

/************************************************************************************
 Copyright (c) 2006-2009, Maarten Mariën

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include "solvers/idsolver/IDSolver.hpp"
#include "solvers/utils/Utils.hpp"
#include "solvers/utils/Print.hpp"

#include "solvers/pcsolver/PCSolver.hpp"

#include "solvers/SATUtils.h"
#include <cmath>

#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

inline void IDSolver::addCycleSource(Var v) {
	if (!isCS[v]) {
		isCS[v] = true;
		css.push(v);
	}
}
inline void IDSolver::clearCycleSources() {
	for (int i = 0; i < css.size(); i++)
		isCS[css[i]] = false;
	css.clear();
}

inline bool IDSolver::canBecomeTrue(Lit l) const {
	return value(l) != l_False;
}
inline bool IDSolver::inSameSCC(Var x, Var y) const {
	return scc[x] == scc[y] && scc[x] != -1;
} //-1 indicates not defined


inline bool IDSolver::isDefInPosGraph(Var v) const {
	return defOcc[v] == POSLOOP || defOcc[v] == BOTHLOOP;
}
inline bool IDSolver::isDefined(Var v) const {
	return defType[v] != NONDEFTYPE;
}
bool IDSolver::isConjunctive(Var v) const {
	return getDefType(v) == CONJ;
}
bool IDSolver::isDisjunctive(Var v) const {
	return getDefType(v) == DISJ;
}
bool IDSolver::isDefinedByAggr(Var v) const {
	return getDefType(v) == AGGR;
}

IDSolver::IDSolver(pPCSolver s) :
	SolverModule(s), aggsolver(NULL), firstsearch(true), prev_conflicts(0), unfoundedsets(0), cycle_sources(0),
			previoustrailatsimp(-1), justifiable_cycle_sources(0),
			cycles(0),
			cycle_sizes(0),
			justify_conflicts(0), // ecnf_mode.def
			nb_times_findCS(0), justify_calls(0), cs_removed_in_justify(0), succesful_justify_calls(0),
			extdisj_sizes(0), total_marked_size(0), posloops(true), negloops(true), adaption_total(0),
			adaption_current(0) {
}

IDSolver::~IDSolver() {
	//reportf("Unfounded sets: %d\n", unfoundedsets);
	deleteList<PropRule> (definition);
}

void IDSolver::notifyVarAdded(int nvars) {
	seen.growTo(nvars, 0);
	//seen2.push(0);

	definition.resize(nvars, NULL);
	reasons.resize(nvars);
	defType.resize(nvars, NONDEFTYPE);
	defOcc.resize(nvars, NONDEFOCC);
	//assert(definition.size()==defType.size());
	disj_occurs.resize(2 * nvars); // May be tested on in findCycleSources().
	conj_occurs.resize(2 * nvars); // Probably not needed anyway...
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
bool IDSolver::addRule(bool conj, Lit head, const vec<Lit>& ps) {
	if (!isPositive(head)) {
		throw idpexception("Negative heads are not allowed.\n");
	}

	if(isDefined(var(head))){
		throw new idpexception("Multiple rules have the same head, which is not allowed!\n");
	}

	if (verbosity() >= 5) {
		reportf("Adding %s rule, %d <- ", conj?"conjunctive":"disjunctive", gprintVar(var(head)));
		for (int i = 0; i < ps.size(); i++) {
			reportf("%s%d ", sign(ps[i])?"-":"",gprintVar(var(ps[i])));
		}
		reportf("\n");
	}

	bool notunsat = true;

	if (ps.size() == 0) {
		Lit h = conj ? head : ~head; //empty set conj = true, empty set disj = false
		vec<Lit> v;
		v.push(h);
		notunsat = getPCSolver()->addClause(v);
	} else {
		//rules with only one body atom have to be treated as conjunctive
		conj = conj || ps.size() == 1;

		PropRule* r = new PropRule(head, ps);
		defdVars.push_back(var(head));
		//defType.growTo(nVars(), NONDEFTYPE);
		//defOcc.growTo(nVars(), NONDEFOCC);
		defType[var(head)] = conj ? CONJ : DISJ;
		//defOcc is initialized when finishing the datastructures
		definition[var(head)] = r;

		//create the completion
		vec<Lit> comp;
		comp.push(head);

		for (int i = 0; i < ps.size(); i++) {
			comp.push(ps[i]);
		}

		if (conj) {
			for (int i = 1; i < comp.size(); i++) {
				comp[i] = ~comp[i];
			}
		} else {
			comp[0] = ~comp[0];
		}

		vec<Lit> temp; //because addclause empties temp
		comp.copyTo(temp);
		notunsat = getPCSolver()->addClause(temp);

		for (int i = 1; notunsat && i < comp.size(); i++) {
			vec<Lit> binclause(2);
			binclause[0] = ~comp[0];
			binclause[1] = ~comp[i];
			notunsat = getPCSolver()->addClause(binclause);
		}
	}
	return notunsat;
}

/*
 * Using the vector "defdVars", initialize all other SAT(ID) additional data structures.
 *
 * @PRE: aggregates have to have been finished
 */
bool IDSolver::finishECNF_DataStructures() {
	notifyInitialized();
	int nvars = nVars();
	/* TODO CHECK REMOVALL!
	definition.resize(nvars, NULL);
	defType.resize(nvars, NONDEFTYPE);
	defOcc.resize(nvars, NONDEFOCC);*/

	//TODO treat definition as the datastructere holding all INPUT rules, where defdvars only contains the currently defined ones.
	//Then a heuristic can be constructed which bump when head vars are assigned e.g.

	//First, go over list of aggregate heads to remove those which are not longer defined
	//(removing them one by one was much too expensive)
	for (int i = 0; i < defdVars.size(); i++) {
		if (toremoveaggrheads.find(defdVars[i]) != toremoveaggrheads.end()) {
			defType[defdVars[i]] = NONDEFTYPE;
			defOcc[defdVars[i]] = NONDEFOCC;
			defdVars[i] = defdVars[defdVars.size() - 1];
			defdVars.pop_back();
			i--;
		}
	}

	if (verbosity() >= 1) {
		reportf("| Number of rules           : %6d                                          |\n",defdVars.size());
	}

	// Initialize scc of full dependency graph
	scc.growTo(nvars, -1);
	vec<bool> incomp(nvars, false);
	vec<Var> stack;
	vec<int> visited(nvars, 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	vec<Var> rootofmixed;
	vec<Var> nodeinmixed;
	int counter = 1;

	for (int i = 0; i < defdVars.size(); i++) {
		if (visited[defdVars[i]] == 0) {
			visitFull(defdVars[i], scc, incomp, stack, visited, counter, true, rootofmixed, nodeinmixed);
		}
	}

	if (verbosity() > 5) {
		reportf("Printing sccs full graph:");
		for (int i = 0; i < nvars; i++) {
			reportf("SCC of %d is %d\n", gprintVar(i), gprintVar(scc[i]));
		}
		reportf("Ended printing sccs. Size of roots = %d, nodes in mixed = %d.\n", rootofmixed.size(), nodeinmixed.size());
	}

	//all var in rootofmixed are the roots of mixed loops. All other are no loops (size 1) or positive loops

	// Initialize scc of positive dependency graph
	for (int i = 0; i < nodeinmixed.size(); i++) {
		incomp[nodeinmixed[i]] = false;
		defOcc[nodeinmixed[i]] = MIXEDLOOP;
		visited[nodeinmixed[i]] = 0;
	}
	stack.clear();
	counter = 1;

	for (int i = 0; i < nodeinmixed.size(); i++) {
		if (visited[nodeinmixed[i]] == 0) {
			visit(nodeinmixed[i], scc, incomp, stack, visited, counter);
		}
	}

	if (verbosity() > 5) {
		reportf("Printing sccs pos graph:");
		for (int i = 0; i < nvars; i++) {
			reportf("SCC of %d is %d\n", gprintVar(i), gprintVar(scc[i]));
		}
		reportf("Ended printing sccs.\n");
	}

	// Determine which literals should no longer be considered defined (according to the scc in the positive graph) + init occurs
	atoms_in_pos_loops = 0;
	disj_occurs.resize(2 * nvars);
	conj_occurs.resize(2 * nvars);

	Lit l;
	vector<Var> reducedVars;
	for (int i = 0; i < defdVars.size(); ++i) {
		Var v = defdVars[i];
		bool isdefd = false;
		switch (getDefType(v)) {
			case DISJ: {
				PropRule& dfn = *definition[v];
				for (int j = 0; j < dfn.size(); ++j) {
					l = dfn[j];
					if (l != dfn.getHeadLiteral()) { //don't look for a justification that is the head literal itself
						disj_occurs[toInt(l)].push_back(v);
					}
					if (isPositive(l) && inSameSCC(v, var(l))) {
						isdefd = true;
					}
				}
				break;
			}
			case CONJ: {
				PropRule& dfn = *definition[v];
				for (int j = 0; j < dfn.size(); ++j) {
					l = dfn[j];
					if (l != dfn.getHeadLiteral()) { //don't look for a justification that is the head literal itself
						conj_occurs[toInt(l)].push_back(v);
					}
					if (isPositive(l) && inSameSCC(v, var(l))) {
						isdefd = true;
					}
				}
				break;
			}
			case AGGR: {
				if (getAggSolver() != NULL) {
					for (vwl::const_iterator j = getAggSolver()->getAggLiteralsBegin(v); !isdefd && j
							< getAggSolver()->getAggLiteralsEnd(v); ++j) {
						if (inSameSCC(v, var((*j).getLit()))) { // NOTE: disregard sign here: set literals can occur both pos and neg in justifications. This could possibly be made more precise for MIN and MAX...
							isdefd = true;
						}
					}
				}
				break;
			}
			default:
				assert(false);
		}

		if (isdefd) { //might occur in a positive loop
			atoms_in_pos_loops++;
			defOcc[v] = defOcc[v] == MIXEDLOOP ? BOTHLOOP : POSLOOP;
			reducedVars.push_back(v);
		} else { //will not occur in a positive loop
			if (defOcc[v] == NONDEFOCC) { //will not occur in a loop
				//IMPORTANT: after this point, disj/conj_occurs might also contain NONDEF links
				//assumes any literal only occurs once!
				if (defType[v] == AGGR) {
					if (getAggSolver() != NULL) {
						for (vwl::const_iterator j = getAggSolver()->getAggLiteralsBegin(v); !isdefd && j
								< getAggSolver()->getAggLiteralsEnd(v); ++j) {
							l = (*j).getLit();
							if (disj_occurs[toInt(l)].size() > 0 && disj_occurs[toInt(l)].back() == v) {
								disj_occurs[toInt(l)].pop_back();
							}
							if (conj_occurs[toInt(l)].size() > 0 && conj_occurs[toInt(l)].back() == v) {
								conj_occurs[toInt(l)].pop_back();
							}
						}
					}
				} else {
					PropRule& dfn = *definition[v];
					for (int j = 0; j < dfn.size(); ++j) {
						l = dfn[j];
						if (disj_occurs[toInt(l)].size() > 0 && disj_occurs[toInt(l)].back() == v) {
							disj_occurs[toInt(l)].pop_back();
						}
						if (conj_occurs[toInt(l)].size() > 0 && conj_occurs[toInt(l)].back() == v) {
							conj_occurs[toInt(l)].pop_back();
						}
					}

					delete definition[v];
					definition[v] = NULL;
				}

				defType[v] = NONDEFTYPE;
			} else if (defOcc[v] == MIXEDLOOP) { //might occur in a mixed loop
				reducedVars.push_back(v);
			}
		}
	}
	defdVars.clear();
	defdVars.insert(defdVars.begin(), reducedVars.begin(), reducedVars.end());

	if (atoms_in_pos_loops == 0) {
		posloops = false;
	}
	if (rootofmixed.size() == 0) {
		negloops = false;
	}

	if (verbosity() >= 1) {
		reportf("| Number of recursive atoms in positive loops : %6d                        |\n",(int)atoms_in_pos_loops);
		if (negloops) {
			reportf("| Mixed loops also exist                                                      |\n");
		}
	}

	if (!negloops && !posloops) {
		return false;
	}

	isCS.growTo(nvars, false);

	if (verbosity() > 5) {
		for (int i = 0; i < defdVars.size(); i++) {
			if (i != 0) {
				reportf(", ");
			}
			Var w = defdVars[i];
			switch (defOcc[w]) {
				case NONDEFOCC:
					reportf("%d=nondef", w);
					break;
				case MIXEDLOOP:
					reportf("%d=mixed", w);
					break;
				case BOTHLOOP:
					reportf("%d=both", w);
					break;
				case POSLOOP:
					reportf("%d=pos", w);
					break;
			}
			if (i % 50 == 0) {
				reportf("\n");
			}
		}
		reportf("\n");
	}

	return true;
}

/**
 * Executes the basic tarjan algorithm for finding strongly connected components (scc). It does this in the FULL dependency graph
 * @pre: only call it on defined nodes that are not already in a found scc
 * @post: root will be a partition that will be the exact partition of SCCs, by setting everything on the stack to the same root in the end
 * @post: the scc will be denoted by the variable in the scc which was visited first
 */
void IDSolver::visitFull(Var i, vec<Var> &root, vec<bool> &incomp, vec<Var> &stack, vec<Var> &visited,
		int& counter, bool throughPositiveLit, vec<int>& rootofmixed, vec<Var>& nodeinmixed) {
	assert(!incomp[i]);
	assert(isDefined(i));
	++counter;
	visited[i] = throughPositiveLit ? counter : -counter;
	root[i] = i;
	stack.push(i);

	switch (getDefType(i)) {
		case DISJ:
		case CONJ: {
			for (int j = 0; j < definition[i]->size(); ++j) {
				Lit l = (*definition[i])[j];
				int w = var(l);
				if (!isDefined(w)) {
					continue;
				}

				if (visited[w] == 0) {
					visitFull(w, root, incomp, stack, visited, counter, isPositive(l), rootofmixed, nodeinmixed);
				} else if (!incomp[w] && !isPositive(l) && visited[i] > 0) {
					visited[i] = -visited[i];
				}
				if (!incomp[w] && abs(visited[root[i]]) > abs(visited[root[w]])) {
					root[i] = root[w];
				}
			}
			break;
		}
		case AGGR: {
			for (vwl::const_iterator j = getAggSolver()->getAggLiteralsBegin(i); j
					< getAggSolver()->getAggLiteralsEnd(i); ++j) {
				Var w = var((*j).getLit());
				if (!isDefined(w)) {
					continue;
				}

				if (visited[w] == 0) {
					visitFull(w, root, incomp, stack, visited, counter, true, rootofmixed, nodeinmixed);
				} else if (!incomp[w] && visited[i] > 0) {
					visited[i] = -visited[i];
				}
				if (!incomp[w] && abs(visited[root[i]]) > abs(visited[root[w]])) {
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
			visited[w] < 0 ? mixed = true : true;
			root[w] = i; //these are the found sccs
			scc.push(w);
			incomp[w] = true;
		} while (w != i);
		if (mixed) {
			rootofmixed.push(i);
			for (int i = 0; i < scc.size(); i++) {
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
	assert(root[i]>=0 && root[i]<nVars());
	assert(!incomp[i]);
	visited[i] = ++counter;
	root[i] = i;
	stack.push(i);

	switch (getDefType(i)) {
		case DISJ:
		case CONJ: {
			for (int j = 0; j < definition[i]->size(); ++j) {
				Lit l = (*definition[i])[j];
				Var w = var(l);
				if (isDefined(w) && i != w && isPositive(l)) {
					if (visited[w] == 0) {
						visit(w, root, incomp, stack, visited, counter);
					}
					if (!incomp[w] && visited[root[i]] > visited[root[w]]) {
						root[i] = root[w];
					}
				}
			}
			break;
		}
		case AGGR: {
			//TODO this can be optimized by using another method which only returns literals possibly in the
			//positive dependency graph.
			for (vwl::const_iterator j = getAggSolver()->getAggLiteralsBegin(i); j
					< getAggSolver()->getAggLiteralsEnd(i); ++j) {
				Var w = var((*j).getLit());
				if (!isDefined(w)) {
					continue;
				}

				if (visited[w] == 0) {
					visit(w, root, incomp, stack, visited, counter);
				}
				if (!incomp[w] && visited[root[i]] > visited[root[w]]) {
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

//@pre: conflicts are empty
bool IDSolver::initAfterSimplify() {
	// This is called after every simplification: maybe more literals have been asserted, so more
	// smaller sccs/more derivations can be found.
	// So we check whether any changes are relevant since last time.
	assert(getPCSolver()->getDecisions().size()==0);
	int currenttrailsize = getPCSolver()->getTrail().size();
	if (currenttrailsize == previoustrailatsimp) {
		/*if(verbosity()>=1){
		 reportf("No new ID simplification necessary.\n");
		 }*/
		return true;
	} else {
		assert(currenttrailsize>previoustrailatsimp);
		previoustrailatsimp = currenttrailsize;
		if (verbosity() >= 2) {
			reportf("Additional ID simplification done.\n");
		}
	}

	// This has to be done before the first choice.

	// NOTE: we're doing a stable model initialization here. No need for a loop.
	justification.clear();
	justification.growTo(nVars());

	// initialize nb_body_lits_to_justify
	vec<Var> usedseen;
	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (isFalse(v)) {
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
	for (int i = 0; i < nVars(); ++i) {
		Lit l = createNegativeLiteral(i);
		if (!isFalse(l)) {
			propq.push(l); // First negative literals are added that are not already false
			//reportf("Justified in initialization: "); gprintLit(l); reportf("\n");
		}
		l = createPositiveLiteral(i);
		if (!isDefInPosGraph(i) && !isFalse(l)) {
			propq.push(l); // Then all non-false non-defined positive literals.
			//reportf("Justified in initialization: "); gprintLit(l); reportf("\n");
		}
	}

	// propagate safeness to defined literals until fixpoint.
	// While we do this, we build the initial justification.
	vec<Lit> heads;
	vec<vec<Lit> > jstf;
	while (propq.size() > 0) {
		Lit l = propq.last(); //only heads are added to the queue
		propq.pop();

		heads.clear();
		jstf.clear();

		propagateJustificationDisj(l, jstf, heads);
		for (int i = 0; i < heads.size(); i++) {
			assert(jstf[i].size()>0);
			//reportf("Justified in initialization: "); gprintLit(heads[i]); reportf("\n");
			changejust(var(heads[i]), jstf[i]);
			propq.push(heads[i]);
		}
		heads.clear();
		jstf.clear();

		propagateJustificationAggr(l, jstf, heads);
		for (int i = 0; i < heads.size(); i++) {
			//reportf("Justified in initialization: "); gprintLit(heads[i]); reportf("\n");
			changejust(var(heads[i]), jstf[i]);
			propq.push(heads[i]);
		}

		propagateJustificationConj(l, propq);
	}

	// vars v that still have nb_body_lits_to_justify[v]>0 can never possibly become true: make them false.
	if (verbosity() >= 2) {
		reportf("Initialization of justification makes these atoms false: [");
	}

	/**
	 * Goes through all definitions and checks whether they can still become true (if they have been
	 * justified). Otherwise, it is checked (overestimation) whether a negative loop might be possible.
	 * If this is not the case, the definition is removed from the data structures.
	 */
	vector<Var> reducedVars;
	bool aggpresent = false;
	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (seen[v] > 0 || isFalse(v)) {
			if (verbosity() >= 2) {
				reportf(" %d", gprintVar(v));
			}
			if (isTrue(v)) {
				return false;
			} else if (isUnknown(v)) {
				getPCSolver()->setTrue(createNegativeLiteral(v), BYDEF);
			}

			if (defOcc[v] == POSLOOP) {
				defOcc[v] = NONDEFOCC;
				defType[v] = NONDEFTYPE;

				PropRule* r = definition[v];
				definition[v] = NULL;
				delete r;

				--atoms_in_pos_loops;
			} else {
				//FIXME is dit wel juist? want de var gaat dan geen justification gekregen hebben
				//maar er kunnen zich ook geen unfounded loops in voordoen, enkel nog
				//wellfoundedness problemen
				defOcc[v] = MIXEDLOOP;
				reducedVars.push_back(v);
			}
		} else {
			reducedVars.push_back(v);
			if (!aggpresent && defType[v] == AGGR) {
				aggpresent = true;
			}
		}
	}
	defdVars.clear();
	defdVars.insert(defdVars.begin(), reducedVars.begin(), reducedVars.end());

	//reconstruct the disj and conj occurs with the reduced number of definitions
	disj_occurs.clear();
	conj_occurs.clear();
	disj_occurs.resize(2 * nVars());
	conj_occurs.resize(2 * nVars());
	for (int i = 0; i < defdVars.size(); ++i) {
		Var v = defdVars[i];
		if (getDefType(v) == CONJ || getDefType(v) == DISJ) {
			PropRule& dfn = *definition[v];
			for (int j = 0; j < dfn.size(); ++j) {
				Lit l = dfn[j];
				if (l != dfn.getHeadLiteral()) { //don't look for a justification that is the head literal itself
					if (getDefType(v) == DISJ) {
						disj_occurs[toInt(l)].push_back(v);
					} else if (getDefType(v) == CONJ) {
						conj_occurs[toInt(l)].push_back(v);
					}
				}
			}
		}
	}

	if (!aggpresent && getAggSolver() != NULL) {
		//getAggSolver()->resetIDSolver();
		aggsolver = NULL;
	}

	for (int i = 0; i < usedseen.size(); i++) {
		seen[usedseen[i]] = 0;
	}

	if (verbosity() >= 2) {
		reportf(" ]\n");
	}

	if (atoms_in_pos_loops == 0) {
		posloops = false;
	}

	if (!posloops && !negloops) {
		getPCSolver()->resetIDSolver();
		if (verbosity() >= 1) {
			reportf("| All recursive atoms falsified in initializations.                           |\n");
		}
	}

	if (verbosity() > 5) {
		for (int i = 0; i < defdVars.size(); i++) {
			if (i != 0) {
				reportf(", ");
			}
			Var w = defdVars[i];
			switch (defOcc[w]) {
				case NONDEFOCC:
					reportf("%d=nondef", w);
					break;
				case MIXEDLOOP:
					reportf("%d=mixed", w);
					break;
				case BOTHLOOP:
					reportf("%d=both", w);
					break;
				case POSLOOP:
					reportf("%d=pos", w);
					break;
			}
			if (i % 50 == 0) {
				reportf("\n");
			}
		}
		reportf("\n");
	}

#ifdef DEBUG
	for (int i = 0; i < defdVars.size(); i++) {
		Var var = defdVars[i];
		assert(defType[var]!=NONDEFTYPE);

		Lit l(createPositiveLiteral(var));
		const vector<Var>& disj = disj_occurs[toInt(l)];
		for (vector<Var>::const_iterator j = disj.begin(); j < disj.end(); j++) {
			assert(getDefType(*j)==DISJ);
		}
		const vector<Var>& conj = conj_occurs[toInt(l)];
		for (vector<Var>::const_iterator j = conj.begin(); j < conj.end(); j++) {
			assert(getDefType(*j)==CONJ);
		}
		assert(justification[var].size()>0 || defType[var]!=DISJ || defOcc[var]==MIXEDLOOP);
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
void IDSolver::propagateJustificationDisj(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads) {
	const vector<Var>& disj = disj_occurs[toInt(l)];
	for (vector<Var>::const_iterator i = disj.begin(); i < disj.end(); i++) {
		const Var& v = *i;
		if (isFalse(v) || seen[v] == 0) {
			continue;
		}
		seen[v] = 0;
		heads.push(createPositiveLiteral(v));
		jstf.push();
		jstf.last().push(l);
	}
}

void IDSolver::propagateJustificationConj(Lit l, vec<Lit>& heads) {
	const vector<Var>& ll = conj_occurs[toInt(l)];
	for (vector<Var>::const_iterator i = ll.begin(); i < ll.end(); i++) {
		const Var& v = *i;
		if (isFalse(v) || seen[v] == 0) {
			continue;
		}
		seen[v]--;
		if (seen[v] == 0) {
			heads.push(createPositiveLiteral(v));
			//reportf("Justified in initialization: "); gprintLit(createPositiveLiteral(v)); reportf("\n");
		}
	}
}

void IDSolver::propagateJustificationAggr(Lit l, vec<vec<Lit> >& jstf, vec<Lit>& heads) {
	if (getAggSolver() == NULL) {
		return;
	}
	getAggSolver()->propagateJustifications(l, jstf, heads, seen);
}

/*_________________________________________________________________________________________________
 |
 |  indirectPropagate : [void]  ->  [CCC]
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
 |
 |	Returns non-owning pointer
 |________________________________________________________________________________________________@*/
rClause IDSolver::indirectPropagate() {
	if (!indirectPropagateNow()) {
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

	if (getPCSolver()->modes().ufs_strategy == breadth_first) {
		for (j = 0; !ufs_found && j < css.size(); j++) {
			if (isCS[css[j]]) {
				ufs_found = unfounded(css[j], ufs);
			}
		}
	} else {
		int visittime = 1; //time at which NO node has been visited yet
		vec<Var> stack;
		seen2.growTo(nVars(), 0);
		/* the seen2 variable is used to indicate:
		 * 		that a value has been visited (and its number is the time at which it was visited
		 * 		0 means not yet visited
		 * 		a negative value means that it has been visited at the abs value and that it has
		 * 		already received a valid justification
		 */
		for (j = 0; !ufs_found && j < css.size(); j++) {//hij komt nooit in het geval dat hij iets op de stack moet pushen, altijd disj unfounded???
			if (isCS[css[j]] && seen[css[j]] == 0) {
				//om geen seen2 nodig te hebben, mag seen niet tegelijk gebruikt kunnen worden in unfounded()
				vec<vec<Lit> > network; //maps a node to a list of nodes that have visited the first one
				//as index, the visited time is used
				network.growTo(visittime + 1);
				network[visittime].push(mkLit(css[j]));
				UFS ret = visitForUFSsimple(css[j], ufs, visittime, stack, seen2, network);
				switch (ret) {
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

	justifiable_cycle_sources += ufs_found ? (j - 1) : j; // This includes those that are removed inside "unfounded".
	succesful_justify_calls += (justify_calls - old_justify_calls);

	rClause confl = nullPtrClause;
	if (ufs_found) {
		if (verbosity() >= 2) {
			reportf("Found an unfounded set of size %d: {",(int)ufs.size());
			for (std::set<Var>::const_iterator it = ufs.begin(); it != ufs.end(); ++it) {
				reportf(" %d",gprintVar(*it));
			}
			reportf(" }.\n");
		}
		cycles++;
		cycle_sizes += ufs.size();
		if (getPCSolver()->modes().defn_strategy == adaptive) {
			adaption_current++; // This way we make sure that if adaption_current > adaption_total, this decision level had indirect propagations.
		}
		confl = assertUnfoundedSet(ufs);
	} else { // Found a witness justification.
		apply_changes();
	}

	return confl;
}

void IDSolver::newDecisionLevel() {
	//Originally checked this after indirectpropagate, which was incorrect, because only at the end of any
	//decision level is there a guarantee of being cyclefree
#ifdef DEBUG
	if(!isCycleFree()) {
		reportf("NOT CYCLE FREE!");
		exit(-1);
	}
#endif
}

/**
 * Cycle sources are the defined variables that have lost support during the
 * preceding unit propagations, and for which a simple supporting replacement
 * justification may not be cycle-free.
 */
void IDSolver::findCycleSources() {
	clearCycleSources();

	if (!firstsearch && prev_conflicts == getPCSolver()->getConflicts() && getPCSolver()->modes().defn_strategy
			== always) {
		const vec<Lit>& trail = getPCSolver()->getTrail();
		int recentindex = getPCSolver()->getStartLastLevel();
		for (int i = recentindex; i < trail.size(); i++) {
			Lit l = trail[i]; //l has become true, so find occurences of ~l

			assert(value(~l)==l_False);

			//TODO should check whether it is faster to use a real watched scheme here: go from justification to heads easily, so this loop only goes over literal which are really justifications
			const vector<Var>& ds = disj_occurs[toInt(~l)];
			for (vector<Var>::const_iterator j = ds.begin(); j < ds.end(); j++) {
				checkJustification(*j);
			}

			if (getAggSolver() != NULL) {
				vector<Var> heads = getAggSolver()->getAggHeadsWithBodyLit(var(~l));
				for (vector<Var>::size_type j = 0; j < heads.size(); j++) {
					checkJustification(heads[j]);
				}
			}
		}
	} else {
		// NOTE: with a clever trail system, we could even after conflicts avoid having to look at all rules.
		firstsearch = false;
		prev_conflicts = getPCSolver()->getConflicts();
		for (int i = 0; i < defdVars.size(); i++) {
			if (defType[defdVars[i]] == DISJ || defType[defdVars[i]] == AGGR) {
				checkJustification(defdVars[i]);
			}
		}
	}
	if (verbosity() >= 2) {
		reportf("Indirect propagations. Verifying %d cycle sources:",css.size());
		for (int i = 0; i < css.size(); ++i) {
			reportf(" %d", gprintVar(css[i]));
		}
		reportf(".\n");
	}
	nb_times_findCS++;
	cycle_sources += css.size();
}

void IDSolver::checkJustification(Var head) {
	if (isCS[head] || isFalse(head) || !isDefInPosGraph(head)) {
		return;
	}

	bool justfalse = false;
	for (int i = 0; !justfalse && i < justification[head].size(); i++) {
		if (isFalse(justification[head][i])) {
			justfalse = true;
		}
	}
	if (!justfalse) {
		return;
	}

	//Incorrect to prune out heads in which Lit is not the justification

	vec<Lit> jstf;
	bool external = true;

	if (defType[head] == DISJ) {
		findJustificationDisj(head, jstf);
	} else {
		assert(defType[head]==AGGR);
		getAggSolver()->findJustificationAggr(head, jstf);
	}
	for (int i = 0; external && i < jstf.size(); i++) {
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
	const PropRule& c = *definition[v];
	int pos = -1;
	for (int i = 0; i < c.size(); i++) {
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
	if (getPCSolver()->modes().defn_strategy != always && !getPCSolver()->totalModelFound()) {
		if (getPCSolver()->modes().defn_strategy == lazy) {
			propagate = false;
		}
		if (getPCSolver()->modes().defn_strategy == adaptive && adaption_current < adaption_total) {
			adaption_current++;
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
	justify_calls++;
	vec<Var> tmpseen; // use to speed up the cleaning of data structures in "Finish"
	Queue<Var> q;
	Var v;

	markNonJustified(cs, tmpseen);
	bool csisjustified = false;

	seen[cs] = 1; //no valid justification can be created just from looking at the body literals
	tmpseen.push(cs);

	if (verbosity() > 5) {
		for (int i = 0; i < defdVars.size(); i++) {
			if (isJustified(defdVars[i])) {
				reportf("Still justified %d\n", gprintVar(defdVars[i]));
			}
		}
	}

	q.insert(cs);
	ufs.clear();
	ufs.insert(cs);
	while (!csisjustified && q.size() > 0) {
		v = q.peek();
		q.pop();
		if (isJustified(v)) {
			continue;
		}
		if (directlyJustifiable(v, ufs, q)) {
			if (verbosity() > 5) {
				reportf("Can directly justify %d\n", gprintVar(v));
			}
			if (propagateJustified(v, cs, ufs)) {
				csisjustified = true;
			}
		}
	}

	for (int i = 0; i < tmpseen.size(); i++) {
		seen[tmpseen[i]] = 0;
	}

#ifdef DEBUG
	for (int i = 0; i < nVars(); i++) {
		assert(seen[i]==0);
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
 * seen is used as a justification mark/counter:
 *
 * seen==0 || negative body literal <=> justified
 */
inline bool IDSolver::isJustified(Lit x) const {
	return isJustified(var(x)) || !isPositive(x);
}
inline bool IDSolver::isJustified(Var x) const {
	return seen[x] == 0;
}

/**
 * Checks whether there is a justification for v given the current justification counters
 */
bool IDSolver::findJustificationDisj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	PropRule& c = *definition[v];
	bool externallyjustified = false;
	currentjust[v] = 1;
	int pos = -1;
	for (int i = 0; !externallyjustified && i < c.size(); i++) {
		if (c.getHeadLiteral() == c[i]) {
			continue;
		}

		if (!isFalse(c[i])) {
			if (!isPositive(c[i]) || currentjust[var(c[i])] == 0) {
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
		currentjust[v] = 0;
	}
	return currentjust[v] == 0;
}

bool IDSolver::findJustificationConj(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	PropRule& c = *definition[v];
	currentjust[v] = 0;
	for (int i = 0; i < c.size(); i++) {
		if (isPositive(c[i]) && currentjust[var(c[i])] != 0) {
			currentjust[v]++;
			nonjstf.push(var(c[i]));
		}
	}
	return currentjust[v] == 0;
}

bool IDSolver::findJustificationAggr(Var v, vec<Lit>& jstf, vec<Var>& nonjstf, vec<Var>& currentjust) {
	currentjust[v] = 1; //used as boolean (0 is justified, 1 is not)
	if (getAggSolver()->directlyJustifiable(v, jstf, nonjstf, currentjust)) {
		currentjust[v] = 0;
	}
	return currentjust[v] == 0;
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

	switch (defType[v]) {
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
		for (int i = 0; i < nonjstf.size(); i++) {
			assert(!isJustified(nonjstf[i]));
			if (inSameSCC(nonjstf[i], v)) {
				if (ufs.insert(nonjstf[i]).second) { //set insert returns true (in second) if the insertion worked (no duplicates)
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
		cs_removed_in_justify++;

		if (k == cs) {
			return true;
		}

		Lit bdl = createPositiveLiteral(k);

		vec<Lit> heads;
		vec<vec<Lit> > jstf;
		propagateJustificationDisj(bdl, jstf, heads);
		propagateJustificationAggr(bdl, jstf, heads);

		for (int i = 0; i < heads.size(); i++) {
			assert(jstf[i].size()>0);
			changejust(var(heads[i]), jstf[i]);
			justifiedq.push(var(heads[i]));
			if (verbosity() > 5) {
				reportf("justified %d\n", gprintVar(var(heads[i])));
			}
		}

		heads.clear();
		propagateJustificationConj(bdl, heads);
		for (int i = 0; i < heads.size(); i++) {
			justifiedq.push(var(heads[i]));
			if (verbosity() > 5) {
				reportf("justified %d\n", gprintVar(var(heads[i])));
			}
		}
	}
	return false;
}

// Change sp_justification: v is now justified by j.
void IDSolver::changejust(Var v, vec<Lit>& j) {
	assert(j.size()>0 || defType[v]==AGGR); //justification can be empty for aggregates
	justification[v].clear();
	j.copyTo(justification[v]);
}

/**
 * Given an unfounded sets, constructs the loop formula:
 * the set of all relevant external literals of the rules with heads in the unfounded set.
 */
void IDSolver::addExternalDisjuncts(const std::set<Var>& ufs, vec<Lit>& loopf) {
#ifdef DEBUG
	assert(loopf.size()==1); //Space for the head/new variable
	for (int i = 0; i < nVars(); i++) { //seen should be cleared
		assert(seen[i]==0);
	}
#endif

	//In seen, we store literals that have been added to the loopf or found not to belong in it.
	//seen[A]==1 indicates that A has been added
	//seen[A]==2 indicates that ~A has been added
	//Both can be added once, because of the assumption that a rule has been simplified to only contain any of them once

	for (std::set<Var>::const_iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		switch (getDefType(*tch)) {
			case CONJ: //
				break;
			case DISJ: {
				PropRule& c = *definition[*tch];
				for (int i = 0; i < c.size(); i++) {
					Lit l = c[i];
					if (seen[var(l)] != (isPositive(l) ? 2 : 1) && ufs.find(var(c[i])) == ufs.end()) {
						assert(isFalse(l));
						loopf.push(l);
						seen[var(l)] = (isPositive(l) ? 2 : 1);
					}
				}
				break;
			}
			case AGGR:
				getAggSolver()->addExternalLiterals(*tch, ufs, loopf, seen);
				break;
			default:
				assert(false);
				throw idpexception("Only AGGR, CONJ or DISJ should be checked for external disjuncts!\n");
				break;
		}
	}

	for (int i = 1; i < loopf.size(); i++) {
		//FIXME added later, should be verified
		getPCSolver()->varBumpActivity(var(loopf[i]));

		seen[var(loopf[i])] = 0;
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

	unfoundedsets++;

	// Create the loop formula: add the external disjuncts (first element will be filled in later).
	vec<Lit> loopf(1);
	addExternalDisjuncts(ufs, loopf);

	// Check if any of the literals in the set are already true, which leads to a conflict.
	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		if (isTrue(*tch)) {
			loopf[0] = createNegativeLiteral(*tch); //negate the head to create a clause
			rClause c = getPCSolver()->createClause(loopf, true);
			getPCSolver()->addLearnedClause(c);
			justify_conflicts++;
			if (verbosity() >= 2) {
				reportf("Adding conflicting loop formula: [ ");
				Print::printClause(c, getPCSolver());
				reportf("].\n");
			}
			//reportf("Conflicting unfounded set found.\n");
			return c;
		}
	}

	// No conflict: then enqueue all facts and their loop formulas.
	if (loopf.size() >= 5) {
		//introduce a new var to represent all external disjuncts: v <=> \bigvee external disj
		Var v = getPCSolver()->newVar();
		if (verbosity() >= 2) {
			reportf("Adding new variable for loop formulas: %d.\n", gprintVar(v));
		}

		// ~v \vee \bigvee\extdisj{L}
		addLoopfClause(createNegativeLiteral(v), loopf);

		// \forall d \in \extdisj{L}: ~d \vee v
		vec<Lit> binaryclause(2);
		binaryclause[1] = createPositiveLiteral(v);
		for (int i = 1; i < loopf.size(); ++i) {
			addLoopfClause(~loopf[i], binaryclause);
		}

		loopf.shrink(2);

		//the end loop formula just contains v
		loopf[1] = createPositiveLiteral(v);
	}

	for (std::set<Var>::iterator tch = ufs.begin(); tch != ufs.end(); tch++) {
		//if (isUnknown(*tch)) { //TODO check if adding this increases/decreases performance
		Lit l = createNegativeLiteral(*tch);
		addLoopfClause(l, loopf);
		assert(!isUnknown(*tch));
		//}
	}

	return nullPtrClause;
}

void IDSolver::addLoopfClause(Lit l, vec<Lit>& lits) {
	lits[0] = l;

	if (getPCSolver()->modes().idclausesaving > 0) {
		reasons[var(l)].clear();
		for (int i = 0; i < lits.size(); i++) {
			reasons[var(l)].push_back(lits[i]);
		}
		if (value(lits[0]) == l_Undef) {
			getPCSolver()->setTrue(lits[0], BYDEF);
		}
	} else {
		rClause c = getPCSolver()->createClause(lits, true);
		getPCSolver()->addLearnedClause(c);

		//if unit propagation is already possible, this might not be detected on time, so help a little
		//MEANING: if lits is already completely false, this clause cannot be added to the store
		int unknown = 0;
		int unknindex = -1;
		bool allfalse = true;
		for (int i = 0; unknown < 2 && i < lits.size(); i++) {
			if (value(lits[i]) == l_Undef) {
				unknown++;
				unknindex = i;
				allfalse = false;
			} else if (value(lits[i]) == l_True) {
				allfalse = false;
			}
		}
		if (allfalse) {
			return;
		}

		if (unknown == 1) {
			getPCSolver()->setTrue(lits[unknindex], BYSAT, c);
		}

		if (verbosity() >= 2) {
			reportf("Adding loop formula: [ ");
			Print::printClause(c, getPCSolver());
			reportf("].\n");
		}
	}
}

void IDSolver::backtrack(const Lit& l) {
	reasons[var(l)].clear();
}

rClause IDSolver::getExplanation(const Lit& l) {
	assert(getPCSolver()->modes().idclausesaving>0);
	vec<Lit> lits;
	for (int i = 0; i < reasons[var(l)].size(); i++) {
		lits.push(reasons[var(l)][i]);
	}
	return getPCSolver()->createClause(lits, true);
}

/* Precondition:  seen[i]==0 for each i.
 * Postcondition: seen[i]  for exactly those i that are ancestors of cs in sp_justification. If modes.defn_search==stop_at_cs, there should not be other cycle sources then cs in the path from added literals to cs.
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
	const vector<Var>& v = disj_occurs[toInt(poslit)];
	for (vector<Var>::const_iterator i = v.begin(); i < v.end(); i++) {
		if (isDefInPosGraph(*i) && var(justification[*i][0]) == x) {
			markNonJustifiedAddVar(*i, cs, q, tmpseen);
		}
	}
	const vector<Var>& w = conj_occurs[toInt(poslit)];
	for (vector<Var>::const_iterator i = w.begin(); i < w.end(); i++) {
		markNonJustifiedAddVar(*i, cs, q, tmpseen);
	}
	if (getAggSolver() != NULL) {
		vector<Var> heads = getAggSolver()->getAggHeadsWithBodyLit(x);
		for (vector<Var>::size_type i = 0; i < heads.size(); i++) {
			vec<Lit>& jstfc = justification[heads[i]];
			for (int k = 0; k < jstfc.size(); k++) {
				if (jstfc[k] == poslit) { // Found that x is actually used in y's justification.
					markNonJustifiedAddVar(heads[i], cs, q, tmpseen);
					break;
				}
			}
		}
	}
}

inline void IDSolver::markNonJustifiedAddVar(Var v, Var cs, Queue<Var> &q, vec<Var>& tmpseen) {
	if (inSameSCC(v, cs) && (getPCSolver()->modes().defn_search == include_cs || v == cs || !isCS[v])) {
		if (seen[v] == 0) {
			seen[v] = 1;
			tmpseen.push(v);
			q.insert(v);
			total_marked_size++;
		} else {
			seen[v]++;
		}

		if (verbosity() > 5) {
			reportf("Not justified %d, times %d\n", gprintVar(v), seen[v]);
		}
	}
}

/**
 * Propagates the changes from supporting to cycle free
 */
inline void IDSolver::apply_changes() {
	if (getPCSolver()->modes().defn_strategy == adaptive) {
		if (adaption_current == adaption_total) {
			adaption_total++; // Next time, skip one decision level extra.
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
	return justification[v];
}

/**
 * Checks whether the aggregate head v has a new external justification (just).
 * If this is the case (all literal in other scc than v or not defined in pos graph), then the new just is added.
 * Otherwise, v is added as a cycle source.
 */
void IDSolver::cycleSourceAggr(Var v, vec<Lit>& just) {
	bool alljustifiedexternally = true;
	for (int i = 0; alljustifiedexternally && i < just.size(); i++) {
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

void IDSolver::notifyAggrHead(Var head) {
	assert(!isDefined(head) && !isInitialized());
	defType[head] = AGGR;
	defOcc[head] = NONDEFOCC;
	defdVars.push_back(head);
}

void IDSolver::removeAggrHead(Var head) {
	assert(!isInitialized());
	if (isDefined(head)) {
		toremoveaggrheads.insert(head);
	}
}

//=================================================================================================
// Debug + etc:
// a literal is a variable shifted one to the left
// a variable is a literal shifted one to the right

inline void IDSolver::print(const PropRule& c) const {
	for (int i = 0; i < c.size(); i++) {
		gprintLit(c[i]);
		fprintf(stderr, " ");
	}
}

/**
 * For debugging purposes, checks for POSITIVE LOOPS.
 */
bool IDSolver::isCycleFree() const {
#ifdef DEBUG
	for (int i = 0; i < nVars(); i++) {
		assert(justification[i].size()>0 || defType[i]!=DISJ || defOcc[i]==MIXEDLOOP);
	}
#endif
	if (getAggSolver() != NULL) {
		if (verbosity() >= 2) {
			reportf("Cycle-freeness checking is not implemented in the presence of recursive aggregates.\n");
		}
		return true;
	}

	if (verbosity() >= 2) {
		reportf("Showing justification for disjunctive atoms. <<<<<<<<<<\n");
		for (int i = 0; i < nVars(); i++) {
			if (isDefined(i) && getDefType(i) == DISJ && defOcc[i] != MIXEDLOOP) {
				gprintLit(mkLit(i, false));
				reportf("<-");
				gprintLit(justification[i][0]);
				reportf("; ");
			}
		}
		reportf(">>>>>>>>>>\n");
	}

	// Verify cycles.
	vector<Var> isfree(nVars(), 0); // per variable. 0 = free, >0 = number of literals in body still to be justified.
	vector<Lit> justified;
	int cnt_nonjustified = 0;
	for (int i = 0; i < nVars(); i++) {
		justified.push_back(mkLit(i, true)); // negative literals are justified anyhow.
		if (!isDefInPosGraph(i)) {
			justified.push_back(mkLit(i, false));
		} else {
			cnt_nonjustified++;
			isfree[i] = getDefType(i) == CONJ ? definition[i]->size() : 1;

			if (getDefType(i) == DISJ) {
				if (value(i) == l_True) {
					assert(value(justification[i][0])!=l_False);
				} else {
					for (int j = 0; j < definition[i]->size(); j++) {
						assert(value(definition[i]->operator [](j))!=l_True);
					}
				}
			} else {
				if (value(i) == l_True) {
					for (int j = 0; j < definition[i]->size(); j++) {
						assert(value(definition[i]->operator [](j))!=l_False);
					}
				} else {
					bool found = false;
					for (int j = 0; !found && j < definition[i]->size(); j++) {
						if (value(definition[i]->operator [](j)) != l_True) {
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

	int idx = 0;
	while (cnt_nonjustified > 0 && idx < justified.size()) {
		Lit l = justified[idx++];

		// Occurrences as justifying literal.
		const vector<Var>& ds = disj_occurs[toInt(l)];
		const vector<Var>& cs = conj_occurs[toInt(l)];
		/*
		 vec<Var> as;
		 if(getAggSolver()!=NULL){
		 getAggSolver()->getHeadsOfAggrInWhichOccurs(var(l), as);
		 }
		 */

		for (vector<Var>::const_iterator i = ds.begin(); i < ds.end(); ++i) {
			Var d = *i;
			assert(defType[d]==DISJ && (!isDefInPosGraph(*i) || justification[d].size()==1));
			if (isfree[d] > 0 && justification[d][0] == l) {
				assert(isfree[d]==1);
				isfree[d] = 0;
				justified.push_back(mkLit(d, false));
				--cnt_nonjustified;
			}
		}
		for (vector<Var>::const_iterator i = cs.begin(); i < cs.end(); ++i) {
			Var c = *i;
			assert(defType[c]==CONJ);
			if (isfree[c] > 0) {
				isfree[c]--;
				if (isfree[c] == 0) {
					justified.push_back(mkLit(c, false));
					--cnt_nonjustified;
				}
			}
		}
		/*
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
			reportf("WARNING: There remain %d literals non-justified.\n",cnt_nonjustified);
		}

		vec<bool> printed;
		printed.growTo(nVars(), false);
		int i = 0;
		while (i < nVars()) {
			if (verbosity() > 2) {
				reportf("Cycle:\n");
			}
			for (; i < nVars() && (!isDefInPosGraph(i) || isfree[i] == 0); i++)
				;

			if (i < nVars()) {
				vec<Var> cycle;
				cycle.push(i);
				int idx = 0;
				while (idx < cycle.size()) {
					Var v = cycle[idx++];
					if (getDefType(v) == DISJ) {
						if (verbosity() >= 2) {
							reportf("D %d justified by ", gprintVar(v));
							gprintLit(justification[v][0]);
							reportf(".\n");
						}
						if (!printed[var(justification[v][0])]) {
							cycle.push(var(justification[v][0]));
						}
					} else if (getDefType(v) == CONJ) {
						if (verbosity() > 2) {
							reportf("C %d has", gprintVar(v));
						}
						PropRule& c = *definition[v];
						for (int j = 0; j < c.size(); j++) {
							Var vj = var(c[j]);
							if (c[j] != c.getHeadLiteral() && isPositive(c[j]) && (isfree[vj] != 0 || printed[vj])) {
								if (verbosity() > 2) {
									reportf(" %d", gprintVar(vj));
								}
								if (!printed[vj]) {
									cycle.push(vj);
								}
							}
						}
						if (verbosity() > 2) {
							reportf(" in its body.\n");
						}
					} else {
						if (verbosity() > 2) {
							reportf("Change aggregate output here (iscyclefree method)"); //TODO change output (and make the method used by the solver
						}
					}
					printed[v] = true;
				}
				for (int j = 0; j < cycle.size(); j++) {
					isfree[cycle[j]] = 0;
				}
			}
		}
	} else {
		if (verbosity() > 2) {
			reportf("OK; justification is cycle free.\n");
		}
	}
	return cnt_nonjustified == 0;
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
	if (!isCycleFree()) {
		if (verbosity() > 1) {
			reportf("A positive unfounded loop exists, so not well-founded!\n");
		}
		return false;
	}

	if (!negloops) {
		if (verbosity() > 1) {
			reportf("Well-founded for positive loops, no negative loops present!\n");
		}
		return true;
	}

	if (getAggSolver() != NULL) {
		if (verbosity() > 1) {
			reportf("For recursive aggregates, only stable semantics are currently supported!\n");
			reportf("Well-foundedness is not checked!\n");
		}

		return true;
	}

	// Initialize scc of full dependency graph
	wfroot.resize(nVars(), -1);
	vector<Var> rootofmixed;
	wfisMarked.resize(nVars(), false);
	//seen is used as justification counters, expected to be a vec of 0 of size nvars

	findMixedCycles(wfroot, rootofmixed);

	if (verbosity() > 1) {
		reportf("general SCCs found");
		for (vector<int>::size_type z = 0; z < wfroot.size(); z++) {
			reportf("%d has root %d\n", gprintVar(z), gprintVar(wfroot[z]));
		}
		reportf("Mixedcycles are %s present: \n", rootofmixed.empty()?"not":"possibly");
	}

	if (rootofmixed.empty()) {
		if (verbosity() > 1) {
			reportf("The model is well-founded!\n");
		}
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
	while (!wffixpoint) {
		wffixpoint = true;

		initializeCounters();
		forwardPropagate(true);
		if (wfmarkedAtoms.empty()) {
			if (verbosity() > 1) {
				reportf("The model is well-founded!\n");
			}
			return true;
		}
		overestimateCounters();
		forwardPropagate(false);
		removeMarks();
		if (wfmarkedAtoms.empty()) {
			if (verbosity() > 1) {
				reportf("The model is well-founded!\n");
			}
			return true;
		}
	}

	for (int i = 0; i < nVars(); i++) {
		seen[i] = 0;
	}

	if (verbosity() > 1) {
		reportf("The model is not well-founded!\n");
	}

	return false;
}

/**
 * Visit the heads of all rules and check the current JUSTIFICATION graph for loops with mixed signs
 * (because of standard propagation, there are no other loops). The head is always positive,
 * so pure negative loops are not possible.
 */
void IDSolver::findMixedCycles(vector<Var> &root, vector<int>& rootofmixed) {
	vector<bool> incomp(nVars(), false);
	stack<Var> stack;
	vector<int> visited(nVars(), 0); // =0 represents not visited; >0 corresponds to visited through a positive body literal, <0 through a negative body literal
	int counter = 1;

	for (int i = 0; i < defdVars.size(); i++) {
		Var v = defdVars[i];
		if (visited[v] == 0) {
			visitWF(v, root, incomp, stack, visited, counter, true, rootofmixed);
		}
	}
}

void IDSolver::visitWF(Var v, vector<Var> &root, vector<bool> &incomp, stack<Var> &stack, vector<Var> &visited,
		int& counter, bool throughPositiveLit, vector<int>& rootofmixed) {
	assert(!incomp[v]);
	++counter;
	visited[v] = throughPositiveLit ? counter : -counter;
	root[v] = v;
	stack.push(v);

	bool headtrue = value(v) == l_True;

	if (defType[v] == AGGR) {
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
	} else if ((headtrue && isConjunctive(v)) || (!headtrue && isDisjunctive(v))) {
		//head is false and disj, or head is true and conj: all body literals are its justification
		for (int i = 0; i < definition[v]->size(); i++) {
			Lit l = definition[v]->operator [](i);
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
		// for DISJ, the justification is already known TODO INCORRECT!
		// for a CONJ, randomly choose one of the false body literals. If there is no loop through it, then it is a good choice.
		//			If there is, it will be found later if another false literal exists without a mixed loop.
		Lit l;
		if (isConjunctive(v)) {
			for (int i = 0; i < definition[v]->size(); i++) {
				Lit l2 = definition[v]->operator [](i);
				if (isFalse(l2)) {
					l = l2;
					break;
				}
			}
		} else {
			for (int i = 0; i < definition[v]->size(); i++) {
				Lit l2 = definition[v]->operator [](i);
				if (isTrue(l2)) {
					l = l2;
					break;
				}
			}
		}
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

		for (vector<Var>::const_iterator i = conj_occurs[toInt(l)].begin(); i < conj_occurs[toInt(l)].end(); i++) {
			mark(*i);
		}
		for (vector<Var>::const_iterator i = conj_occurs[toInt(~l)].begin(); i < conj_occurs[toInt(~l)].end(); i++) {
			mark(*i);
		}

		//false DISJ with -l in body, true DISJ with l as just
		for (vector<Var>::const_iterator i = disj_occurs[toInt(l)].begin(); i < disj_occurs[toInt(l)].end(); i++) {
			//Var head = *i;
			//if ((isTrue(head) && justification[head][0] == l) || isFalse(head)) {
				mark(*i);
			//}
		}
		for (vector<Var>::const_iterator i = disj_occurs[toInt(~l)].begin(); i < disj_occurs[toInt(~l)].end(); i++) {
			//Var head = *i;
			//if ((isTrue(head) && justification[head][0] == ~l) || isFalse(head)) {
				mark(*i);
			//}
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
	for (set<Var>::iterator i = wfmarkedAtoms.begin(); i != wfmarkedAtoms.end(); i++) {
		Var v = *i;
		seen[v] = 0;
		bool canbepropagated = false;
		for (int j = 0; !canbepropagated && j < definition[v]->size(); j++) {
			Lit bl = definition[v]->operator [](j);
			if (wfisMarked[var(bl)]) {
				seen[v]++;
			} else if (isFalse(bl) && defType[v] == CONJ) {
				canbepropagated = true;
			} else if (isTrue(bl) && defType[v] == DISJ && var(bl) != v) {
				canbepropagated = true;
			}
		}
		if (seen[v] == 0 || canbepropagated) {
			seen[v] = 0;
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
		for (vector<Var>::const_iterator i = disj_occurs[toInt(l)].begin(); i < disj_occurs[toInt(l)].end(); i++) {
			Var head = *i;
			if (wfisMarked[head]) {
				wfqueue.push(createPositiveLiteral(head));
				seen[head] = 0;
			}
		}

		//if CONJ and counter gets 0, then head will be true, so add true head to queue
		for (vector<Var>::const_iterator i = conj_occurs[toInt(l)].begin(); i < conj_occurs[toInt(l)].end(); i++) {
			Var head = *i;
			if (wfisMarked[head] && --seen[head] == 0) {
				wfqueue.push(createPositiveLiteral(head));
			}
		}

		l = ~l;

		//Literal l has become false, so for all rules with body literal l and marked head,
		//if DISJ and counter gets 0, then head will be false, so add false head to queue
		for (vector<Var>::const_iterator i = disj_occurs[toInt(l)].begin(); i < disj_occurs[toInt(l)].end(); i++) {
			Var head = *i;
			if (wfisMarked[head] && --seen[head] == 0) {
				wfqueue.push(createNegativeLiteral(head));
			}
		}

		//if CONJ, then head will be false, so add false head to queue and set counter to 0
		for (vector<Var>::const_iterator i = conj_occurs[toInt(l)].begin(); i < conj_occurs[toInt(l)].end(); i++) {
			Var head = *i;
			if (wfisMarked[head]) {
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
	for (set<Var>::iterator i = wfmarkedAtoms.begin(); i != wfmarkedAtoms.end(); i++) {
		Var v = *i;
		assert(seen[v] > 0);

		for (int j = 0; j < definition[v]->size(); j++) {
			Lit bdl = definition[v]->operator [](j);
			if (wfisMarked[var(bdl)] && !isPositive(bdl) && v != var(bdl)) {
				if (defType[v] == CONJ) {
					seen[v]--;
				} else {
					seen[v] = 0;
				}
			}
		}

		if (seen[v] == 0) {
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
	for (set<Var>::iterator i = wfmarkedAtoms.begin(); i != wfmarkedAtoms.end(); i++) {
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
void IDSolver::changeJustificationsTarjan(Var definednode, Lit firstjustification, vec<vec<Lit> >& network, vec<
		int>& vis) {
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
		for (int i = 0; i < network[visitedAtTarjan(var(just), vis)].size(); i++) {
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

inline bool IDSolver::visitedEarlierTarjan(Var x, Var y, const vec<Var>& vis) const {
	int x1 = vis[x] > 0 ? vis[x] : -vis[x];
	int y1 = vis[y] > 0 ? vis[y] : -vis[y];
	return x1 < y1;
}

inline bool IDSolver::visitedTarjan(Var x, const vec<Var>& vis) const {
	return vis[x] != 0;
}

inline int IDSolver::visitedAtTarjan(Var x, const vec<Var>& vis) const {
	return vis[x] > 0 ? vis[x] : -vis[x];
}

inline bool IDSolver::hasJustificationTarjan(Var x, const vec<Var>& vis) const {
	return vis[x] < 0;
}

/////////////
//Finding unfounded checks by
//validjust indicates both that the element is already in a justification or is in another found component (in which case it might also be false, not requiring a justification)
//TODO werkt niet voor aggregaten
UFS IDSolver::visitForUFSsimple(Var v, std::set<Var>& ufs, int& visittime, vec<Var>& stack, vec<Var>& vis, vec<
		vec<Lit> >& network) {
	vis[v] = visittime;
	int timevisited = visittime;
	visittime++;

	DefType type = getDefType(v);

	if (type == AGGR) {
		return OLDCHECK;
	}
	assert(type==CONJ || type==DISJ);

	PropRule* c = definition[v];
	if (verbosity() >= 1) {
		print(*c);
	}

	Lit definedChild;
	bool childfound = false;

	for (int i = 0; i < c->size(); i++) {
		DefType childtype = getDefType(var(c->operator [](i)));
		Lit l = c->operator [](i);
		if (var(l) == v) {
			continue;
		} //rule head or identical body atom
		if (childtype == AGGR) {
			return OLDCHECK;
		}
		if (!isDefInPosGraph(var(c->operator [](i))) || !inSameSCC(var(l), v) || hasJustificationTarjan(var(l),
				vis)) {
			if (!isFalse(l) && type == DISJ) {
				changeJustificationsTarjan(v, l, network, vis);
				return NOTUNFOUNDED;
			}
		}
		if (type == CONJ) {
			if (childfound) {
				definedChild = l;
				childfound = true;
			} else {
				return OLDCHECK;
			}
		}
	}

	stack.push(v);

	if (type == CONJ) {
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
		for (int i = 0; i < c->size(); i++) {
			Var child = var(c->operator [](i));
			if (child == v) {
				continue;
			}
			if (!(getDefType(child) == CONJ || getDefType(child) == DISJ)) {
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
				for (std::set<Var>::iterator i = ufs.begin(); i != ufs.end(); i++) {
					Var x = *i;
					fprintf(stderr, "%d:%c", x << 1, isTrue(x) ? '1' : (isFalse(x) ? '0' : 'X'));
				}
				fprintf(stderr, "\n");
			}
			return UFSFOUND;
		} else {
			int containsx = 0;
			for (int i = 0; i < c->size(); i++) {
				if (x == var(c->operator [](i))) {
					containsx++;
				}
			}
			if (containsx > 1) { //there is a loop of length 1, so x itself is an UFS
				if (verbosity() >= 4) {
					fprintf(stderr, "ufsfound: ");
					for (std::set<Var>::iterator i = ufs.begin(); i != ufs.end(); i++) {
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

///////
// PRINT INFORMATION
///////

void IDSolver::printStatistics() const {
reportf	("cycles                : %-12" PRIu64 "\n", cycles);
	reportf("cycle conflicts       : %-12" PRIu64 "\n", justify_conflicts);
	reportf("avg cycle size        : %4.2f\n", (float)cycle_sizes/cycles);
	reportf("avg extdisj size      : %4.2f\n", (float)extdisj_sizes/cycles);
	reportf("justify runs          : %-12" PRIu64 "   (%4.2f /cycle)\n", justify_calls, (float)justify_calls/cycles);
	reportf("avg. justify searchsp.: %6.2f lits\n", (float)total_marked_size/justify_calls);
	reportf("cycle sources         : %-12" PRIu64 "\n", cycle_sources);
	reportf("                      : %4.2f found per run of findCycleSources()\n", (float)nb_times_findCS/cycle_sources);
	reportf("                      : %4.2f removed per justify run\n", (float)cs_removed_in_justify/justify_calls);
	reportf("                      : %4.2f treated per loop\n", (float)succesful_justify_calls/nb_times_findCS);
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
//	CCC c = definition[v];
//	//PropRule* c = definition[v];
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

