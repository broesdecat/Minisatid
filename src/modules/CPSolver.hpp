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

namespace Gecode{
	template<class T>
	class DFS;
}

namespace MinisatID {
class TermIntVar;
typedef std::vector<TermIntVar> vtiv;
class CPScript;

class CPSolverData;

class LitTrail{
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
	const std::vector<Lit>& getTrail() const { return trail; }
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
	CPSolverData* 		solverdata; //OWNING pointer

	LitTrail			trail;

	std::map<Lit, std::vector<Lit>::size_type > propreason;

	bool				searchedandnobacktrack;

	Gecode::DFS<CPScript>* 		savedsearchengine;

public:
			CPSolver	(PCSolver * pcsolver);
	virtual ~CPSolver	();

	bool 	add		(const InnerIntVarEnum& form);
	bool 	add		(const InnerIntVarRange& form);
	bool 	add		(const InnerCPBinaryRel& form);
	bool 	add		(const InnerCPBinaryRelVar& form);
	bool 	add		(const InnerCPSumWeighted& form);
	bool 	add		(const InnerCPCount& form);
	bool 	add		(const InnerCPAllDiff& form);

	void 	getVariableSubstitutions(std::vector<VariableEqValue>& varassignments);

	// Propagator methods
	void 	finishParsing	(bool& present, bool& unsat);
	void 	notifyNewDecisionLevel();
	void 	notifyBacktrack(int untillevel);
	rClause notifypropagate();
	rClause getExplanation	(const Lit& p);
	void 	printStatistics	() const;
	const char* getName		() const { return "CP-solver"; }
	void 	printState		() const;
	Var 	notifyBranchChoice	(const Var& var) const { return var; }
	rClause notifyFullAssignmentFound() { return nullPtrClause; }
	int		getNbOfFormulas	() const;


	// Search methods
	rClause findNextModel	();

private:
	void 	checkHeadUniqueness() const;

	rClause propagateReificationConstraints();

	rClause genFullConflictClause();

	rClause notifySATsolverOfPropagation(const Lit& p);
	rClause propagateFinal	(bool usesavedengine);

	const CPSolverData& getData	() const { return *solverdata; }
	CPSolverData& 		getData	() { return *solverdata; }
	const CPScript&		getSpace() const;
	CPScript&			getSpace();
	TermIntVar 			convertToVar	(uint term) const;
	vtiv				convertToVars	(const std::vector<uint>& terms) const;
};

}

#endif /* CPSOLVER_HPP_ */
