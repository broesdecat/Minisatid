/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "modules/DPLLTmodule.hpp"

#include <set>
#include <map>

namespace Gecode {
template<class T>
class DFS;
}

namespace MinisatID {
class TermIntVar;
typedef std::vector<TermIntVar> vtiv;
class CPScript;

class ReifiedConstraint;
class Constraint;
class NonReifiedConstraint;

class CPSolverData;

class LitTrail {
private:
	std::vector<std::vector<Lit>::size_type> trailindexoflevel;
	std::vector<Lit> trail;
	std::map<Var, lbool> values;

public:
	LitTrail();
	void newDecisionLevel();
	void backtrackDecisionLevels(int untillevel);
	void propagate(const Lit& lit);
	lbool value(const Lit& lit) const;
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

	LitTrail trail;

	std::map<Lit, std::vector<Lit>::size_type> propreason;

	bool searchedandnobacktrack;

	Gecode::DFS<CPScript>* savedsearchengine;

	std::set<Var> heads;

public:
	CPSolver(PCSolver * pcsolver);
	virtual ~CPSolver();

	bool add(const IntVarEnum& form);
	bool add(const IntVarRange& form);
	bool add(const CPBinaryRel& form);
	bool add(const CPBinaryRelVar& form);
	bool add(const CPSumWeighted& form);
	bool add(const CPCount& form);
	bool add(const CPAllDiff& form);

	void getVariableSubstitutions(std::vector<VariableEqValue>& varassignments);

	// Propagator methods
	virtual void accept(ConstraintVisitor& visitor){ throw notYetImplemented("Accept"); }
	rClause getExplanation(const Lit& p);
	void notifyNewDecisionLevel();
	void notifyBacktrack(int untillevel, const Lit& decision);
	rClause notifypropagate();

	// Search methods
	rClause findNextModel();

private:
	void checkHeadUniqueness(ReifiedConstraint const * const c);
	void add(ReifiedConstraint* c);
	void add(NonReifiedConstraint* c);
	void addConstraint(Constraint* c);

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
	TermIntVar convertToVar(uint term) const;
	vtiv convertToVars(const std::vector<uint>& terms) const;
};

}

#endif /* CPSOLVER_HPP_ */
