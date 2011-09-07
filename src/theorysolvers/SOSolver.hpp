/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef SOSOLVER_H_
#define SOSOLVER_H_

#include "utils/Utils.hpp"
#include "theorysolvers/LogicSolver.hpp"

namespace MinisatID {

/**
 * USEFUL EXTRA PROPAGATION RULES FROM PAPER "An algorithm for QBF and experimental evaluation":
 *
 * forall reduction in qdimacs format: if a clause only contains universally quantified
 * literals, then it has to be a tautology or it is unsat (so anyway it can be dropped)
 * => need to store the quantifier of variables
 *
 * all clauses only containing existentially quantified vars have to be SAT or whole problem is UNSAT.
 * => SAT CALL
 * Initially, take all clauses only containing EQ vars.
 * Later, take all clauses containing EQ vars and decided UQ vars.
 * => Simulate by taking full theory, replace all literals = \lnot UQ var with a new var (#atoms+var), and make
 * 		all true that have not yet been decided.
 * Then incremental SAT solving with assumptions
 *
 * if the theory with all universally quantified vars dropped is SAT, then the whole theory is SAT
 * => SAT CALL
 * Initially, take all clauses with all UQ left out
 * Later, take all clauses containing EQ vars and decided UQ vars, leaving out the undecided ones.
 * => Simulate by taking full theory, replace all literals = \lnot AQ var with a new var (#atoms+var), and make
 * 		all false that have not yet been decided.
 * Then incremental SAT solving with assumptions
 *
 * monotone literals can be immediately assigned a value
 *
 * propagation if a clause only contains one existentially quantified literal and only later universally
 * quantified literals.
 *
 * something called pairwise falsity
 *
 */

class ModSolver;
typedef std::vector<ModSolver*> vmsolvers;

enum modhierstate {NEW, LOADINGHIER, LOADINGREST, ALLLOADED};

class SOSolver: public MinisatID::LogicSolver{
private:
	vmsolvers 	 solvers;
	modhierstate state;	//stores the current state of the parsing.

public:
	SOSolver				(SolverOption modes, MinisatID::WrapperPimpl& inter);
	virtual ~SOSolver		();

	void 	finishParsing	(bool& unsat);
	bool 	isRoot			(const ModSolver* solver) const;
	void 	addModel		(const InnerModel& model);
	bool 	simplify		();
	bool 	solve			(const litlist& assumptions, const ModelExpandOptions& options);

	SATVAL	add		(int modid, Var v);
	SATVAL	add		(int modid, const InnerDisjunction& sentence);
	SATVAL	add		(int modid, const InnerRule& sentence);
	SATVAL	add		(int modid, const InnerWLSet& sentence);
	SATVAL	add		(int modid, const InnerAggregate& sentence);
	SATVAL	add		(int modid, const InnerReifAggregate& sentence);
	SATVAL	add		(int modid, const InnerRigidAtoms& sentence);
	SATVAL	add		(int modid, const InnerSubTheory& sentence);

	virtual void	notifyNonDecisionVar(Var var) { }//FIXME

	//Get information on hierarchy
	ModSolver* getModSolver	(vsize modid) const { checkexistsModSolver(modid); return solvers[modid];}

	void 	printStatistics	() const;
	void 	printTheory(std::ostream& stream) { assert(false); }

private:
	ModSolver& getModSolverDuringAdding(int modid);
	void	verifyHierarchy		();
	void	checkexistsModSolver(vsize modid) const;
	bool	existsModSolver		(vsize modid) const { return modid<solvers.size() && solvers[modid]!=NULL; }
};

}

#endif /* SOSOLVER_H_ */
