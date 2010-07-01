/*
 * CPSolver.hpp
 *
 *  Created on: Jun 22, 2010
 *      Author: broes
 */

#ifndef CPSOLVER_HPP_
#define CPSOLVER_HPP_

#include "solvers/PCSolver.hpp"

class PCSolver;

namespace CP {

class CPIntVar{
	IntVar var;
public:
	void propagate(CPConstraint* constr);
	void backtrack(CPConstraint* constr);
};

class CPConstraint{
private:
	CPIntVar* var;
	CPRelation relation;
	int integer;

public:
	enum CPRelation
	{
		EQ,
		NE,
		LE,
		LT,
		GE,
		GT
	};

	CPConstraint();
	~CPConstraint();

	void propagate();
	void backtrack();

	CPRelation 	getRelation	() const { return relation; }
	CPIntVar*	getVar		() const { return var; }
	int 		getInteger	() const { return integer; }

	bool operator==(const CPConstraint& constr) const{
		if(constr.getRelation()!=getRelation()){
			return false;
		}
		if(constr.getVar()!=getVar()){
			return false;
		}
		if(constr.getInteger()!=getInteger()){
			return false;
		}
		return true;
	}
};

/**
 * Class to interface with cp propagation (and who knows, search) engines.
 *
 * Interfacing with gecode:
 * 		include the correct hh files => http://www.gecode.org/doc-latest/reference/PageUsage.html
 *
 * 		gecode works as follows:
 * 			a "Space" obejct keeps the search space, domain, variables, ...
 * 			constraints, vars and domains can be added to the space
 * 			space has an operation "status" which propagates until fixpoint or failure
 */
class CPSolver {
	PCSolver * pcsolver;
	//map<int, CPConstraint> mapatomtoexpr;
	//map<CPConstraint, int> mapexprtoatom;

public:
	CPSolver(PCSolver * pcsolver);
	virtual ~CPSolver();

	propagateLiteral(Lit l);

private:
	/**
	 * Probably implement with a list of intvars, their original domains and a starting integer atom number
	 */
	CPConstraint* findConstraint(Lit l);
	Lit findAtom(CPConstraint* c);
};

}

#endif /* CPSOLVER_HPP_ */
