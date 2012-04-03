/****************************************************************************************[Solver.h]
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

#ifndef Minisat_ClausePropagator_h
#define Minisat_ClausePropagator_h

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "utils/Options.h"
#include "SolverTypes.hpp"

/*AB*/
#include <vector>
#include <iostream>
#include <set>
#include <list>
#include <map>
#include "modules/DPLLTmodule.hpp"

typedef std::vector<Minisat::Lit> litlist;
/*AE*/

namespace MinisatID {
class PCSolver;
class ConstraintVisitor;
}

namespace Minisat {

//=================================================================================================
// Solver -- the main class:

class ClausePropagator: public MinisatID::Propagator {
private:
	uint64_t learnts_literals, clauses_literals;
public:
	/*AB*/
	std::vector<Lit> rootunitlits; // basic reverse trail for unit clauses
	void saveState();
	void resetState();
	void printClause(const CRef c) const;
	void addLearnedClause(CRef c); // don't check anything, just add it to the clauses and bump activity
	void removeClause(CRef cr); // Detach and free a clause.
	CRef makeClause(const vec<Lit>& lits, bool b) {
		return ca.alloc(lits, b);
	}
	CRef getClause(int i) const {
		return clauses[i];
	}
	int nbClauses() const {
		return clauses.size();
	}
	int getClauseSize(CRef cr) const {
		return ca[cr].size();
	}
	Lit getClauseLit(CRef cr, int i) const {
		MAssert(0<=i && i<getClauseSize(cr));
		return ca[cr][i];
	}

	//PROPAGATOR CODE
	// TODO split up in search and propagator
	virtual void accept(MinisatID::ConstraintVisitor& visitor) {
	}// FIXME

	CRef getExplanation(const Lit& l) {
		// FIXME return reason(var(l));
	}
	void finishParsing(bool& present);
	void notifyBacktrack(int untillevel, const Lit& decision) {
		Propagator::notifyBacktrack(untillevel, decision);
	}
	CRef notifypropagate();
	void printStatistics() const;
	int getNbOfFormulas() const {
		return nClauses();
	}

	virtual void notifyNewDecisionLevel() {
	}
	virtual CRef notifyFullAssignmentFound() {
		MAssert(false);
		return CRef_Undef;
	}

	/*AE*/

	// Constructor/Destructor:
	//
	ClausePropagator(/*AB*/MinisatID::PCSolver* s/*AE*/);
	virtual ~ClausePropagator();

	void addClause(vec<Lit>& ps); // Add a clause to the solver without making superflous internal copy. Will
								   // change the passed vector 'ps'.

								   // Solving:
								   //
	void simplify(); // Removes already satisfied clauses.
	int nClauses() const; // The current number of original clauses.
	int nLearnts() const; // The current number of learnt clauses.

	// Memory managment:
	//
	virtual void garbageCollect();
	void checkGarbage(double gf);
	void checkGarbage();

protected:
	void claDecayActivity(); // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.

	/*AB*/
	void addToClauses(CRef cr, bool learnt);
	/*AE*/

	struct Watcher {
		CRef cref;
		Lit blocker;
		Watcher(CRef cr, Lit p) :
				cref(cr), blocker(p) {
		}
		bool operator==(const Watcher& w) const {
			return cref == w.cref;
		}
		bool operator!=(const Watcher& w) const {
			return cref != w.cref;
		}
	};

	struct WatcherDeleted {
		const ClauseAllocator& ca;
		WatcherDeleted(const ClauseAllocator& _ca) :
				ca(_ca) {
		}
		bool operator()(const Watcher& w) const {
			return ca[w.cref].mark() == 1;
		}
	};

	// Solver state:
	//
	vec<CRef> clauses; // List of problem clauses.
	vec<CRef> learnts; // List of learnt clauses.
	double cla_inc; // Amount to bump next clause with.
	double var_inc; // Amount to bump next variable with.
	OccLists<Lit, vec<Watcher>, WatcherDeleted> watches; // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
	int qhead; // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
	int simpDB_assigns; // Number of top-level assignments since last execution of 'simplify()'.
	int64_t simpDB_props; // Remaining number of propagations that must be made before next execution of 'simplify()'.
	bool remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

	ClauseAllocator ca;

	// Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
	// used, exept 'seen' wich is used in several places.
	//
	vec<char> seen;
	vec<Lit> add_tmp;

	// TODO add max limit to learnt clauses!
	double max_learnts;
	double learntsize_adjust_confl;
	int learntsize_adjust_cnt;

	/*AB*/
	bool savedok;
	int savedlevel, savedclausessize, savedqhead;
	vec<int> savedtraillim;
	vec<Lit> savedtrail;
	/*AE*/

	// Main internal methods:
	//
	void reduceDB(); // Reduce the set of learnt clauses.
	void removeSatisfied(vec<CRef>& cs); // Shrink 'cs' to contain only non-satisfied clauses.

	// Maintaining Variable/Clause activity:
	//
	/*AB*///void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead./*AE*/
	void varBumpActivity(Var v, double inc); // Increase a variable with the current 'bump' value.
	/*AB*///void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value./*AE*/
	/*AB*///void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead./*AE*/
	void claBumpActivity(Clause& c); // Increase a clause with the current 'bump' value.

	// Operations on clauses:
	//
	void attachClause(CRef cr); // Attach a clause to watcher lists.
	void detachClause(CRef cr, bool strict = false); // Detach a clause to watcher lists.
	bool locked(const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
	bool satisfied(const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

	void relocAll(ClauseAllocator& to);

private:
	int clause_decay, garbage_frac; // FIXME check these
};

//=================================================================================================
// Implementation of inline methods:

inline bool ClausePropagator::locked(const Clause& c) const { /*FIXME return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c;*/ }

inline void ClausePropagator::claDecayActivity() {
	cla_inc *= (1 / clause_decay);
}
inline void ClausePropagator::claBumpActivity(Clause& c) {
	if ((c.activity() += cla_inc) > 1e20) {
		// Rescale:
		for (int i = 0; i < learnts.size(); i++)
			ca[learnts[i]].activity() *= 1e-20;
		cla_inc *= 1e-20;
	}
}

inline void ClausePropagator::checkGarbage(void) {
	return checkGarbage(garbage_frac);
}
inline void ClausePropagator::checkGarbage(double gf) {
	if (ca.wasted() > ca.size() * gf) {
		garbageCollect();
	}
}

inline int ClausePropagator::nClauses() const {
	return clauses.size();
}
inline int ClausePropagator::nLearnts() const {
	return learnts.size();
}

}

#endif //Minisat_ClausePropagator_h
