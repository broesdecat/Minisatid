/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef MODSOLVER_H_
#define MODSOLVER_H_

#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

#include "wrapper/InterfaceImpl.hpp"

namespace MinisatID {

class Solution;

class PCSolver;
class SOSolver;
class ModSolver;

typedef std::vector<ModSolver*> vmsolvers;
typedef vmsolvers::size_type modindex;
typedef std::vector<modindex> vmodindex;

/**
 * Each modsolver has an id, a parent and a number of children
 * The topmost solver has no parent and id 0 and is created the moment the header is parsed
 *
 * The ids are substracted by one to get their position in the std::std::vector
 *
 * parsing process:
 * read statements of the form
 * A ID1 ID2 ATOM* 0 or E ID1 ID2 ATOM* 0
 * indicating a forall (A) or existantial (E) quantification of the atoms in ATOM* for a modal solver ID1 with parent ID2
 */

struct AV{
	Var atom;
	lbool value;

	AV(Var a): atom(a), value(l_Undef){}
};

/**
 * BASIC MODAL SOLVER ALGORITHM:
 * each model solver MS has a pcsolver PS at same level and a number of modal solver at the next lower level MSC (MS Children)
 *
 * MS:finishparsingdown
 * 		-> PC:finishparsing
 * 		-> MCS:finishparsingdown
 * MS:finishparsing: noop <= ONLY CALLED FROM PS
 *
 * MS:simplifydown
 * 		-> PC:simplify
 * 		-> MCS:simplifydown
 * MS:simplify: noop  <= ONLY CALLED FROM PS
 *
 * MS:propdown
 * 		store in assumptions, remember it came from above
 *
 * MS:propdownatend
 * 		-> PC:search providing assumptions
 * 		-> PC:backtrackTo(0)
 *
 * MS:propagate <= ONLY CALLED FROM PS
 * 		-> add to trail
 * 		-> MCS:propagatedown
 *
 * MS:propagateatend <= ONLY CALLED FROM PS
 * 		-> MCS:propagatedownatend
 *
 * MS:backtrackDecisionLevels <= ONLY CALLED FROM PS
 * 		-> remove from trail
 * 		-> MCS:backtrackFromAbove
 *
 * MS:backtrackdown
 */

class ModSolver: public Propagator, public MinisatID::WrapperPimpl{
private:
	bool 		init, hasparent, searching;
	std::vector<Var> registeredvars;

	AV			head;
	std::vector<Var>	atoms; //atoms which are rigid within this solver

	modindex 	id, parentid;
	vmodindex 	children;
	SOSolver* 	modhier;	//NON-OWNING POINTER!

	litlist 	assumptions;
	std::vector<bool> propfromabove; //Indicates whether this literal was propagated by the parent

	std::vector<std::vector<Lit> > trail; //Trail of propagations, necessary because backtrack is still by literal

	virtual void addModel(const InnerModel& model);

public:
	ModSolver(modindex child, Var head, SOSolver* mh);
	virtual ~ModSolver();

	SATVAL	add		(Var v);
	SATVAL	add		(const InnerDisjunction& sentence);
	SATVAL	add		(const InnerRule& sentence);
	SATVAL	add		(const InnerWLSet& sentence);
	SATVAL	add		(const InnerAggregate& sentence);
	SATVAL	add		(const InnerReifAggregate& sentence);
	SATVAL	add		(const InnerRigidAtoms& sentence);
	SATVAL	addChild(int childid);

	void	setParent		(modindex id);
	void 	setNbModels		(int nb);

	//Propagator methods
	const char* getName				()	const	{ return "modal operator"; }
	void 		printState			() const;
	void 		finishParsing		(bool& present, bool& unsat);
	rClause		notifypropagate		();
	void 		notifyNewDecisionLevel	();
	void 		notifyBacktrack		(int untillevel, const Lit& decision);
	rClause 	getExplanation		(const Lit& l) { assert(false); return nullPtrClause; /*TODO NOT IMPLEMENTED*/ };
	rClause 	notifyFullAssignmentFound(){ return nullPtrClause; } // TODO should check wellfoundedness here
	int			getNbOfFormulas		() const { return children.size(); }



	//Model solver specific
	/**
	 * Propagation coming from the parent solver: propagate it through the tree, until a conflict is found.
	 * SHOULD also return unit propagated implied rigid atoms.
	 */
	rClause 	propagateDown	(Lit l);
	void 		backtrackFromAbove(Lit l);
	void 		finishParsingDown(bool& unsat);
	bool 		propagateDownAtEndOfQueue(litlist& confldisj);

	bool 		solve			(const litlist& assumptions, const ModelExpandOptions& options);

	//Necessary because child of wrapperpimpl
	virtual MinisatID::LogicSolver* getSolver() const { assert(false); return NULL;}


	//PRINTING
	/**
	 * Workflow: parents propagates some literal down
	 * if not all rigid atoms or head known:
	 * 		do unit propagation in sat solver
	 * 		after unit propagation: any new rigid atom/head propagations are propagated UP
	 *
	 * if all rigid atoms and head are known
	 * 		search in sat solver
	 * 		this can only results in conflicts, not in new propagations
	 *
	 * propagate by sat solver -> propagate in this mod solver by propagating it to all modal solvers.
	 *
	 * SAT-solver should contains all atoms occurring in its theory, all heads of the children and all
	 * rigid atoms of the children. It should also decide them all.
	 *
	 * The model of a theory is the interpretation of all atoms decided by the root SAT solver.
	 */
	void 		printModel		();

	bool		hasParent		()	const 	{ return hasparent; }
	Var 		getHead			()	const 	{ assert(hasparent); return head.atom; }
	lbool 		getHeadValue	()	const	{ assert(hasparent); return head.value; }
	modindex 	getId			()	const	{ return id; }
	modindex 	getPrintId		()	const	{ return id+1; }
	modindex	getParentId		()	const	{ return parentid; }
	modindex	getParentPrintId()	const	{ return parentid+1; }
	const std::vector<Var>& getAtoms	()	const	{ return atoms; }
	const vmodindex& 	getChildren		()	const	{ return children; }
	const SOSolver& 	getModSolverData()	const	{ return *modhier; }

private:
	void 		addVar			(const Lit& l)		{ add(var(l)); }
	void 		addVars			(const litlist& a);

	SOSolver& 	getNonConstModSolverData()	{ return *modhier; }

	void		adaptValuesOnPropagation(Lit l);
	void 		doUnitPropagation(const litlist&);
	bool 		search			(const litlist&, bool search = true);
	bool 		analyzeResult	(bool result, bool allknown, litlist& confldisj);
};

}

#endif// MODSOLVER_H_
