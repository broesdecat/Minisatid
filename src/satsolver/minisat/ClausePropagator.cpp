/***************************************************************************************[Solver.cc]
 Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 Copyright (c) 2007-2010, Niklas Sorensson

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

#include <cmath>

#include "mtl/Sort.h"

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "utils/Options.h"

#include <vector>
#include <iostream>
#include <sstream>
#include <cstdarg>
#include <algorithm>

#include "utils/Utils.hpp"
#include "utils/Print.hpp"
#include "theorysolvers/PCSolver.hpp"
#include "ClausePropagator.hpp";

using namespace std;
using namespace MinisatID;

using namespace Minisat;

ClausePropagator::ClausePropagator(/*AB*/PCSolver* s/*AE*/)
		: Propagator(s, "clausepropagator"),
		  watches(WatcherDeleted(ca)){
	getPCSolver().accept(this, EV_PROPAGATE);
}

ClausePropagator::~ClausePropagator(){
	// TODO
}

/*AB*/
void ClausePropagator::finishParsing(bool& present) {
	simplify();
}

void ClausePropagator::addLearnedClause(CRef rc) {
	Clause& c = ca[rc];
	if (c.size() > 1) {
		addToClauses(rc, true);
		attachClause(rc);
		claBumpActivity(c);
		if (modes().verbosity >= 3) {
			clog <<"Learned clause added: ";
			printClause(rc);
			clog <<"\n";
		}
	} else { // Adding literal true at level 0
		MAssert(c.size()==1);
		getPCSolver().backtrackTo(0);
		vec<Lit> ps;
		ps.push(c[0]);
		addClause(ps);
	}
}

struct permute{
	int newposition;
	Lit value;
	permute(int newpos, Lit value): newposition(newpos), value(value){
	}
};

struct lessthan_permute{
	bool operator() (const permute& lhs, const permute& rhs){
		return lhs.newposition<rhs.newposition;
	}
};

// NOTE: do not reimplement as sort with a random comparison operator, comparison should be CONSISTENT on consecutive calls!
void permuteRandom(vec<Lit>& lits){
	vector<permute> newpositions;
	for(int i=0; i<lits.size(); ++i){
		newpositions.push_back(permute(rand(), lits[i]));
	}
	std::sort(newpositions.begin(), newpositions.end(), lessthan_permute());
	for(int i=0; i<lits.size(); ++i){
		lits[i] = newpositions[i].value;
	}
}

void ClausePropagator::addClause(vec<Lit>& ps) {
	if (getPCSolver().isUnsat()){
		return;
	}

	int nonfalsecount = 0;
	if(getPCSolver().getCurrentDecisionLevel()>0){
		for(int i=0; i<ps.size() && nonfalsecount<2; ++i){
			if(not isFalse(ps[i])){
				nonfalsecount++;
			}
		}
		if(nonfalsecount==0){
			getPCSolver().backtrackTo(0);
			addClause(ps);
		}
	}

	sort(ps); // NOTE: remove duplicates

	if(getPCSolver().getCurrentDecisionLevel()==0){
		// Check satisfaction and remove false literals
		Lit p;
		int i, j;
		for (i = j = 0, p = lit_Undef; i < ps.size(); i++){
			if (value(ps[i]) == l_True || ps[i] == ~p){
				return;
			}else if (value(ps[i]) != l_False && ps[i] != p){
				ps[j++] = p = ps[i];
			}
		}
		ps.shrink(i - j);
	}

	// NOTE: sort randomly to reduce dependency on grounding and literal introduction mechanics (certainly for lazy grounding)
	permuteRandom(ps);

	if (ps.size() == 0) {
		return;
	} else if (ps.size() == 1) {
		if(getPCSolver().getCurrentDecisionLevel()>0){
			rootunitlits.push_back(ps[0]);
		}
		// FIXME checkedEnqueue(ps[0]);
		if(getPCSolver().getCurrentDecisionLevel()==0){ // NOTE: do not do unit propagation assuming root level if it is not!
			if(getPCSolver().propagate() != CRef_Undef){
				getPCSolver().notifyUnsat();
			}
			return;
		}
	} else {
		CRef cr = ca.alloc(ps, false);
		addToClauses(cr, false);
		attachClause(cr);
	}
}

CRef ClausePropagator::notifypropagate() {
	// FIXME copy code from Solver
}

/*AB*/
void ClausePropagator::addToClauses(CRef cr, bool learnt) {
	if (learnt) {
		learnts.push(cr);
	} else {
		clauses.push(cr);
	}
}

void sw(Clause& c, int from, int to){
	MAssert(c.size()>from && c.size()>to);
	auto temp = c[from];
	c[from] = c[to];
	c[to] = temp;
}

void ClausePropagator::attachClause(CRef cr) {
	auto& c = ca[cr];
	MAssert(c.size() > 1);

	if(getPCSolver().getCurrentDecisionLevel()>0 && not c.learnt()){ // If Level > 0 and an input clause, reorder the watches so the first two are unknown or the most recently chosen ones
		int firstnonfalseindex = -1, secondnonfalseindex = -1, mostrecentfalseindex = -1, mostrecentfalselevel = -1;
		for(int i=0; i<c.size(); ++i){
			if(isFalse(c[i])){
				if(getPCSolver().getLevel(var(c[i]))>mostrecentfalselevel){
					mostrecentfalselevel = getPCSolver().getLevel(var(c[i]));
					mostrecentfalseindex = i;
				}
			}else{
				if(firstnonfalseindex==-1){
					firstnonfalseindex = i;
				}else if(secondnonfalseindex==-1){
					secondnonfalseindex = i;
				}
			}
		}

		MAssert(firstnonfalseindex!=-1 && not isFalse(c[firstnonfalseindex]));
		sw(c, firstnonfalseindex, 0);
		MAssert(not isFalse(c[0]));

		if(secondnonfalseindex!=-1){
			MAssert(secondnonfalseindex!=-1 && not isFalse(c[secondnonfalseindex]));
			sw(c, secondnonfalseindex, 1);
			MAssert(not isFalse(c[1]));
		}else{ // Clause is unit, so should add the latest false as watch AND have to propagate!
			if(mostrecentfalseindex==0){
				mostrecentfalseindex = firstnonfalseindex;
			}
			MAssert(mostrecentfalseindex!=-1 && isFalse(c[mostrecentfalseindex]));
			sw(c, mostrecentfalseindex, 1);
			MAssert(isFalse(c[1]));
			if(not isTrue(c[0])){ // NOTE: important! The watch has already fired, so otherwise it would be lost!
				getPCSolver().setTrue(c[0], this, cr);
			}
		}
	}

	if(not c.learnt()){
		MAssert(not isFalse(c[1]) || not isFalse(c[0]));
	}
	watches[~c[0]].push(Watcher(cr, c[1]));
	watches[~c[1]].push(Watcher(cr, c[0]));
	if (c.learnt())
		learnts_literals += c.size();
	else
		clauses_literals += c.size();

	if(not c.learnt() || (not isFalse(c[1]) || not isFalse(c[0]))){
		// FIXME checkDecisionVars(c);
	}
}

void ClausePropagator::detachClause(CRef cr, bool strict) {
	const Clause& c = ca[cr];
	if (c.size() < 2) {
		printClause(cr);
		std::clog << "clausesize: " << c.size() << "\n";
	}MAssert(c.size() > 1);

	if (strict) {
		remove(watches[~c[0]], Watcher(cr, c[1]));
		remove(watches[~c[1]], Watcher(cr, c[0]));
	} else {
		// Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
		watches.smudge(~c[0]);
		watches.smudge(~c[1]);
	}

	if (c.learnt())
		learnts_literals -= c.size();
	else
		clauses_literals -= c.size();
}

/*AB*/
void ClausePropagator::saveState() {
	// FIXME
	/*savedok = ok;
	savedlevel = decisionLevel();
	savedclausessize = clauses.size();
	remove_satisfied = false;
	savedqhead = qhead;
	trail_lim.copyTo(savedtraillim);
	trail.copyTo(savedtrail);*/
}

void ClausePropagator::resetState() {
	//FIXME is this correct and sufficient?
	// FIXME add again
	/*ok = savedok;
	cancelUntil(savedlevel);
	qhead = savedqhead;
	trail.clear();
	savedtrail.copyTo(trail);
	trail_lim.clear();
	savedtraillim.copyTo(trail_lim);*/

	//Remove new clauses
	for (int i = savedclausessize; i < clauses.size(); i++) {
		removeClause(clauses[i]);
	}
	clauses.shrink(savedclausessize);

	//Remove learned clauses //TODO only forgetting the new learned clauses would also do and be better for learning!
	for (int i = 0; i < learnts.size(); i++) {
		removeClause(learnts[i]);
	}
	learnts.clear();
}
/*AE*/

void ClausePropagator::removeClause(CRef cr) {
	Clause& c = ca[cr];
	detachClause(cr);
	// Don't leave pointers to free'd memory!
	if (locked(c)){
		// FIXME vardata[var(c[0])].reason = CRef_Undef;
	}
	c.mark(1);
	ca.free(cr);
}

bool ClausePropagator::satisfied(const Clause& c) const {
	for (int i = 0; i < c.size(); i++){
		if (value(c[i]) == l_True){
			return true;
		}
	}
	return false;
}

/*_________________________________________________________________________________________________
 |
 |  reduceDB : ()  ->  [void]
 |
 |  Description:
 |    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
 |    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
 |________________________________________________________________________________________________@*/
struct reduceDB_lt {
	ClauseAllocator& ca;
	reduceDB_lt(ClauseAllocator& ca_)
			: ca(ca_) {
	}
	bool operator ()(CRef x, CRef y) {
		return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
	}
};
void ClausePropagator::reduceDB() {
	int i, j;
	double extra_lim = cla_inc / learnts.size(); // Remove any clause below this activity

	sort(learnts, reduceDB_lt(ca));
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++) {
		Clause& c = ca[learnts[i]];
		if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
			removeClause(learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	learnts.shrink(i - j);
	checkGarbage();
}

void ClausePropagator::removeSatisfied(vec<CRef>& cs) {
	int i, j;
	for (i = j = 0; i < cs.size(); i++) {
		Clause& c = ca[cs[i]];
		if (satisfied(c))
			removeClause(cs[i]);
		else
			cs[j++] = cs[i];
	}
	cs.shrink(i - j);
}

/*_________________________________________________________________________________________________
 |
 |  simplify : [void]  ->  [bool]
 |
 |  Description:
 |    Simplify the clause database according to the current top-level assigment. Currently, the only
 |    thing done here is the removal of satisfied clauses, but more things can be put here.
 |________________________________________________________________________________________________@*/
void ClausePropagator::simplify() {
	MAssert(getPCSolver().getCurrentDecisionLevel() == 0);

	if (getPCSolver().isUnsat() || getPCSolver().propagate() != CRef_Undef){
		getPCSolver().notifyUnsat();
		return;
	}

	// FIXME if (nAssigns() == simpDB_assigns || (simpDB_props > 0)){
		//return;
	//}

	// Remove satisfied clauses:
	removeSatisfied(learnts);
	if (remove_satisfied){  // Can be turned off.
		removeSatisfied(clauses);
	}
	checkGarbage();
	// FIXME rebuildOrderHeap();

	// FIXME simpDB_assigns = nAssigns();
	// FIXME simpDB_props = clauses_literals + learnts_literals; // (shouldn't depend on stats really, but it will do for now)
}

/*AB*/
void ClausePropagator::printClause(CRef rc) const {
	const Clause& c = ca[rc];
	bool begin = true;
	for (int i = 0; i < c.size(); i++){
		if(not begin){
			clog <<" & ";
		}
		begin = false;
		clog <<print(c[i], value(c[i]), getPCSolver());
	}
	clog <<"\n";
}
/*AE*/

//=================================================================================================
// Garbage Collection methods:
void ClausePropagator::relocAll(ClauseAllocator& to) {
	// All watchers:
	//
	// for (int i = 0; i < watches.size(); i++)
	watches.cleanAll();
	for (int v = 0; v < nVars(); v++)
		for (int s = 0; s < 2; s++) {
			Lit p = mkLit(v, s);
			// printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
			vec<Watcher>& ws = watches[p];
			for (int j = 0; j < ws.size(); j++)
				ca.reloc(ws[j].cref, to);
		}

	// All reasons:
	//
	// FIXME
	/*for (int i = 0; i < trail.size(); i++) {
		Var v = var(trail[i]);

		if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
			ca.reloc(vardata[v].reason, to);
	}*/

	// All learnt:
	//
	for (int i = 0; i < learnts.size(); i++)
		ca.reloc(learnts[i], to);

	// All original:
	//
	for (int i = 0; i < clauses.size(); i++)
		ca.reloc(clauses[i], to);
}

void ClausePropagator::garbageCollect() {
	// Initialize the next region to a size corresponding to the estimated utilization degree. This
	// is not precise but should avoid some unnecessary reallocations for the new region:
	ClauseAllocator to(ca.size() - ca.wasted());

	relocAll(to);
	if (modes().verbosity >= 2)
		fprintf(stderr, "|  Garbage collection:   %12d bytes => %12d bytes             |\n", ca.size() * ClauseAllocator::Unit_Size,
				to.size() * ClauseAllocator::Unit_Size);
	to.moveTo(ca);
}
/*AE*/
