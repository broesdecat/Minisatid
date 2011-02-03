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

#ifndef MODSOLVER_H_
#define MODSOLVER_H_

#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

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

class ModSolver: public DPLLTmodule{
private:
	bool 		hasparent, searching;

	AV			head;
	std::vector<Var>	atoms; //atoms which are rigid within this solver

	modindex 	id, parentid;
	PCSolver*	solver;
	vmodindex 	children;
	SOSolver* 	modhier;	//NON-OWNING POINTER!

	vec<Lit> 	assumptions;
	std::vector<bool> propfromabove; //Indicates whether this literal was propagated by the parent

	std::vector<std::vector<Lit> > trail; //Trail of propagations, necessary because backtrack is still by literal

public:
	ModSolver(modindex child, Var head, SOSolver* mh);
	virtual ~ModSolver();

	bool 				addAtoms		(const std::vector<Var>& atoms);
	void 				addChild		(modindex child);
	void				setParent		(modindex id);

	void 				setNbModels		(int nb);

	//data initialization
	void				addVar			(Var v);
	bool 				addClause		(vec<Lit>& lits);
	bool 				addRule			(bool conj, Lit head, vec<Lit>& lits);
	bool 				addSet			(int setid, vec<Lit>& lits, std::vector<Weight>& w);
	bool 				addAggrExpr		(Lit head, int set_id, const Weight& bound, AggSign boundsign, AggType type, AggSem defined);

	void 				notifyVarAdded	(uint64_t nvars) { /*Is NOT DOWN!*/}

	void 				finishParsing	(bool& present, bool& unsat){};
	void 				finishParsingDown(bool& present, bool& unsat);

	bool 				simplify		()	{ return true;};
	bool 				simplifyDown	();


	void 				newDecisionLevel();

	rClause 			getExplanation	(const Lit& l) { return nullPtrClause; /*TODO NOT IMPLEMENTED*/ };

	/**
	 * Propagation coming from the parent solver: propagate it through the tree, until a conflict is found.
	 * SHOULD also return unit propagated implied rigid atoms.
	 */
	rClause 			propagateDown	(Lit l);
	bool	 			propagateDownAtEndOfQueue(vec<Lit>& confldisj);
	rClause 			propagate		(const Lit& l);
	rClause 			propagateAtEndOfQueue();

	void 				backtrackDecisionLevels	(int nblevels, int untillevel);
	void 				backtrackFromAbove(Lit l);

	bool 				solve			(const vec<Lit>& assumptions, Solution* sol);


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
	void 				printModel		();
	void 				print			() const;
	void 				printStatistics	() const 	{ /*Do NOT print lower ones here*/};

	//GETTERS
	const char* 		getName			()	const	{ return "modal operator"; }
	bool				hasParent		()	const 	{ return hasparent; }
	Var 				getHead			()	const 	{ assert(hasparent); return head.atom; }
	lbool 				getHeadValue	()	const	{ assert(hasparent); return head.value; }
	modindex 			getId			()	const	{ return id; }
	modindex 			getPrintId		()	const	{ return id+1; }
	modindex			getParentId		()	const	{ return parentid; }
	modindex			getParentPrintId()	const	{ return parentid+1; }
	const std::vector<Var>& getAtoms	()	const	{ return atoms; }
	const vmodindex& 	getChildren		()	const	{ return children; }
	const SOSolver& 	getModSolverData()	const	{ return *modhier; }

private:
	void 				addVar			(Lit l)		{ addVar(var(l)); }
	void 				addVars			(vec<Lit>& a);

	void				adaptValuesOnPropagation(Lit l);
	void 				doUnitPropagation(const vec<Lit>&);
	bool 				search			(const vec<Lit>&, bool search = true);
	bool 				analyzeResult	(bool result, bool allknown, vec<Lit>& confldisj);
};

}

#endif// MODSOLVER_H_