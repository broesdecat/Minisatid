/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/ModSolver.hpp"

#include "utils/Utils.hpp"
#include "utils/Print.hpp"
#include <vector>
#include <algorithm>

#include "theorysolvers/PCSolver.hpp"

#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;

//Important: The head variable does not occur in this theory, so should NOT automatically be
//added as a var in it.
/**
 * Constructs a ModSolver, with a given head, index and hierarchy pointer. A PCSolver is initialized.
 */
// TODO set nbofmodels of subsolvers to 1 or All!
// TODO set their verbosity to 0 if not debugging
ModSolver::ModSolver(Atom head, PCSolver* parent, PCSolver* subsolver, const std::vector<Atom>& rigidatoms)
		: Propagator(parent, "modal solver"), searching(false), rigidatoms(rigidatoms), head(head), child(subsolver) {
	trail.push_back(vector<Lit>());
}

ModSolver::~ModSolver() {
}

void ModSolver::finishParsing(){
	getParent().accept(this, mkLit(head.atom, true), SLOW);
	getParent().accept(this, mkLit(head.atom, false), SLOW);
	for (auto atom : rigidatoms) {
		atoms.push_back(atom);
		getParent().accept(this, mkLit(atom, true), SLOW);
		getParent().accept(this, mkLit(atom, false), SLOW);
	}
	//Creates a bool-vector mapping each atom to whether it was propagated from above or from this theory
	propfromabove = vector<bool>(atoms.size(), false);

	getParent().accept(this);
	getParent().accept(this, EV_DECISIONLEVEL);
	getParent().accept(this, EV_BACKTRACK);
}

void ModSolver::notifyNewDecisionLevel() {
	trail.push_back(vector<Lit>());
}

bool ModSolver::search(const litlist& assumpts, bool ) {
	/*
	 * In the end, we would want to propagate level by level, without having to restart the whole process
	 * every time. This requires a startsearch and continuesearch procedure in the SAT-solver
	 * As this is rather tedious, we will delay it until necessary.
	 bool result = true;
	 if(startindex==-1){
	 result = getParent().startSearch();
	 startindex = 0;
	 }
	 for(; result && startindex<assumptions.size(); ++startindex){
	 result = getParent().propagate(assumptions[startindex]);
	 }
	 if(search && result){
	 searching = true;
	 result = getParent().continueSearch();
	 searching = false;
	 }

	 return result;*/

  child->clearAssumptions();
  for(auto l: assumpts){
    child->addAssumption(l);
  }
	searching = true;
	auto result = child->solve(true);
	searching = false;
	if(result==l_Undef){
		throw idpexception("Subtheory search did not reach a conclusion.");
	}
	return result==l_True;
}

/**
 * Returns non-owning pointer
 */
rClause ModSolver::notifypropagate() {
	rClause confl = nullPtrClause;
	if (!searching) {
		vector<Lit> v = getParent().getDecisions();
		//TODO propagate up WITH reason
	}

	while (hasNextProp() && confl == nullPtrClause) {
		const Lit& l = getNextProp();
		if (verbosity() > 4) {
			clog << ">>Propagated " << toString(l) << " from PC in mod " << getID() << ".\n";
		}

		trail.back().push_back(l);
		confl = propagateDown(l);
	}

	if (confl != nullPtrClause) {
		return confl;
	}

	//In future, we might want to delay effectively propagating and searching in subfolders to the point where the
	//queue is empty, so we will need a propagateDown and a propagateDownEndOfQueue
	bool noconflict = true;
	Disjunction confldisj({ });
	assert(confldisj.literals.size()==0);
	noconflict = propagateDownAtEndOfQueue(confldisj.literals);

	if (not noconflict) {
		confl = getParent().createClause(confldisj, true);
		getParent().addConflictClause(confl);
	}
	return confl;
}

/**
 * Propagates l to be true from the parent modal solver.
 * As long as the PC-solver is still propagating, this solver should not do anything more than store
 * the propagation, as modal satisfiability checking can be much more expensive. So this solver always
 * returns NULL.
 */
rClause ModSolver::propagateDown(Lit l) {
	if (verbosity() > 4) {
		clog << toString(l) << " propagated down into modal solver " << getID() << ".\n";
	}

	/**
	 * Checks whether l is relevant to this modal theory (the head or a rigid atom).
	 * If this is the case, it adapts the data structures.
	 */

	//Adapt head value
	if (getHead() == var(l)) {
		MAssert(getHeadValue()==l_Undef);
		head.value = !sign(l) ? l_True : l_False;
	}

	//adapt rigid atoms value
	for (vector<AV>::size_type i = 0; i < atoms.size(); ++i) {
		if (var(l) == atoms[i]) {
			propfromabove[i] = true;
			assumptions.push_back(l);
			break;
		}
	}

	return nullPtrClause;
}

/**
 * Notifies the modal solver that propagation of the parent solver are finished. At this point, the modal solver
 * will be propagated.
 * Returns true if no conflict ensues
 */
bool ModSolver::propagateDownAtEndOfQueue(litlist& confldisj) {
	if (verbosity() > 4) {
		clog << "End of queue propagation down into modal solver" << getID() << "\n";
	}

	bool allknown = false;

	/*TODO future:
	 bool result;
	 if(!allknown){
	 result = doUnitPropagation(assumpts);
	 }else{
	 result = search(assumpts);
	 }
	 */

	if ((uint) assumptions.size() == getAtoms().size() && getHeadValue() != l_Undef) {
		allknown = true;
		searching = false;
	}

  // TODO: state saving is now replaced by assumption-controlled constraints. Please test whether the Modsolver still works!
	// getParent().saveState(); //IMPORTANT
	bool result = search(assumptions, allknown);
	result = analyzeResult(result, allknown, confldisj);
	// getParent().resetState();

	if (verbosity() > 4) {
		clog << "Finished checking solver " << getID() << ": " << (result ? "no conflict" : "conflict") << ".\n";
	}

	return result;
}

void ModSolver::notifyBacktrack(int untillevel, const Lit& decision) {
	if (verbosity() > 4) {
		clog << "Backtracking from PC in mod " << getID() << " to level " << untillevel << "\n";
	}

	while (trail.size() > ((uint) (untillevel + 1))) {
		//IMPORTANT: backtrack in REVERSE trail order! from latest to earliest!
		for (auto i = trail.back().rbegin(); i < trail.back().rend(); ++i) {
			backtrackFromAbove(*i);
		}
		trail.pop_back();
	}

	Propagator::notifyBacktrack(untillevel, decision);
}

/**
 * For backtracking on rigid atoms, there are two possibilities:
 * 		the backtracking comes from above, so it has to be done
 * 		the backtracking is from the PC-solver
 * 			in this case, it might be that it was propagated or chosen by the PC Solver, in which case it should be backtracked
 * 						or it might be that it was propagated from above, in which case it should NOT be backtracked
 * 			currently, this is solved by storing an boolean remembering whether it was propagated from above or from the pc solver
 */
void ModSolver::backtrackFromAbove(Lit l) {
	if (verbosity() > 4) {
		searching = false;
		clog << "Backtracking " << toString(l) << " from above in mod " << getID() << "\n";
	}

	if (var(l) == getHead() && getHeadValue() != l_Undef) {
		head.value = l_Undef;
	}
	for (vector<AV>::size_type i = 0; i < atoms.size(); ++i) {
		if (atoms[i] == var(l)) {
			if (propfromabove[i] && var(l) == var(assumptions.back())) {
				assumptions.pop_back();
				//startindex--;
				int solverlevel = child->getLevel(var(l));
				if (solverlevel >= 0) { //otherwise it was not propagated!
					child->backtrackTo(solverlevel);
				}
				propfromabove[i] = false;
				break;
			} else {
#ifndef NDEBUG
				for (uint j = 0; j < assumptions.size(); ++j) {
					assert(var(assumptions[j])!=var(l));
				}
#endif
			}
		}
	}
}

/**
 * Important, returns a clause constructed to be added to the PARENT solver: the vars are NOT necessarily
 * decision vars in this PC solver
 * Returns true if no conflict ensues
 */
bool ModSolver::analyzeResult(bool result, bool allknown, litlist& confldisj) {
	bool conflict = false;
	//if no model found and should be sat or if model found, should be unsat and all values are known
	if (getHeadValue() == l_True && !result) {
		conflict = true;
	}
	if (getHeadValue() == l_False && result && allknown) {
		conflict = true;
	}

	if (conflict) { //conflict between head and body
		//TODO can the clause learning be improved?
		MAssert(confldisj.size()==0);
		if (getHeadValue() != l_Undef) {
			confldisj.push_back(mkLit(getHead(), getHeadValue() == l_True));
		}
		//TODO order of lits in conflict depends on order of assumptions and on order of propagations by parent
		for (uint i = 0; i < assumptions.size(); ++i) {
			if (propfromabove[i]) {
				confldisj.push_back(~assumptions[i]);
			}
		}
		MAssert(confldisj.size()>0);
	}

	return !conflict;
}
