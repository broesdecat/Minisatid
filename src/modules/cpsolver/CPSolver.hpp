/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include "modules/DPLLTmodule.hpp"

#include <set>
#include <queue>
#include <map>

namespace Gecode {
template<class T>
class DFS;
}

namespace MinisatID {
class TermIntVar;
class CPScript;

class ReifiedConstraint;
class Constraint;
class NonReifiedConstraint;

class CPSolverData;

class LitTrail {
private:
	std::vector<std::vector<Lit>::size_type> trailindexoflevel;
	std::vector<Lit> trail;

public:
	LitTrail();
	void newDecisionLevel();
	void backtrackDecisionLevels(int untillevel);
	void propagate(const Lit& lit);
	const std::vector<Lit>& getTrail() const {
		return trail;
	}
};

/**
 * Class to interface with cp propagation (and who knows, search engines).
 *
 * Interfacing with gecode:
 * 		include the correct hh files => http://www.gecode.org/doc-latest/reference/PageUsage.html
 *
 * 		gecode works as follows:
 * 			a "Space" object stores the search space, domain, variables, ...
 * 			constraints, vars and domains can be added to the space
 * 			space has a "status" operation which propagates until fixpoint or failure
 */
class CPSolver: public Propagator {
private:
	CPSolverData* solverdata; //OWNING pointer

	bool addedconstraints;
	LitTrail trail, savedtrail;

	std::map<Lit, std::vector<Lit>::size_type> propreason;

	bool searchedandnobacktrack;
	Gecode::DFS<CPScript>* savedsearchengine;
	CPScript* model;

	std::set<Atom> heads;

	std::vector<bool> level2hasspace;

	std::queue<ReifiedConstraint*> recentreifconstr;

	bool searchstarted; // To prevent CP search during parsing

public:
	CPSolver(PCSolver * pcsolver);
	virtual ~CPSolver();

	bool add(const IntVarEnum& form);
	bool add(const IntVarRange& form);
	bool add(const CPBinaryRel& form);
	bool add(const CPBinaryRelVar& form);
	bool add(const CPSumWeighted& form);
	bool add(const CPProdWeighted& form);
	bool add(const CPCount& form);
	bool add(const CPAllDiff& form);
	bool add(const CPElement& form);

	void getVariableSubstitutions(std::vector<VariableEqValue>& varassignments);

	// Propagator methods
	virtual void accept(ConstraintVisitor& visitor);
	rClause getExplanation(const Lit& p);
	void notifyNewDecisionLevel();
	void notifyBacktrack(int untillevel, const Lit& decision);
	rClause notifypropagate();
	rClause notifyFullAssignmentFound();

	void saveState() {
		addedconstraints = false;
		savedtrail = trail;
	}
	void resetState() {
		if (addedconstraints) {
			throw notYetImplemented("Saving and resetting new gecode-constraints added during search.");
		}
		trail = savedtrail;
	}
	virtual int getNbOfFormulas() const;

	// Search methods
	bool hasData() const;
	rClause findNextModel();

private:
	void checkHeadUniqueness(ReifiedConstraint const * const c);
	void add(ReifiedConstraint* c);
	void add(NonReifiedConstraint* c);
	void addedConstraint();

	rClause propagateReificationConstraints();

	rClause genFullConflictClause();

	rClause notifySATsolverOfPropagation(const Lit& p);
	rClause propagateFinal(bool usesavedengine);

	const CPSolverData& getData() const {
		return *solverdata;
	}
	CPSolverData& getData() {
		return *solverdata;
	}
	const CPScript& getSpace() const;
	CPScript& getSpace();
	TermIntVar convertToVar(VarID term) const;
	std::vector<TermIntVar> convertToVars(const std::vector<VarID>& terms) const;
};

}
