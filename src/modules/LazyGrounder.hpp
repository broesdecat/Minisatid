/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef LAZYGROUNDER_HPP_
#define LAZYGROUNDER_HPP_

#include <vector>
#include "utils/Utils.hpp"
#include "modules/DPLLTmodule.hpp"

/*
 * How does it work:
 * have a vector with full clauses
 * have a vector with "grounded" clauses and an index of where we are in the full clause
 * make the grounded clauses 1-watched
 *
 * during propagate:
 * 		if a clause becomes fully false, extends its grounding until it can become true, set that as watch
 * 		if it cannot be made true any more, backtrack to the appropriate level and add the full clause to the solver
 */

namespace MinisatID{

class PCSolver;
class Watch;

class LazyResidual;

class LazyResidual: public Propagator{
private:
	LazyGroundingCommand* monitor;
	Atom residual;
	Value watchedvalue;

public:
	LazyResidual(PCSolver* engine, Atom var, Value watchedvalue, LazyGroundingCommand* monitor);

	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause getExplanation(const Lit&) { MAssert(false); return nullPtrClause;}
	virtual void notifyNewDecisionLevel() { MAssert(false); }
	virtual void notifyBacktrack(int, const Lit&){ MAssert(false); }
	virtual int getNbOfFormulas() const { return 1; }
};

class LazyTseitinClause: public Propagator{
private:
	int clauseID; // The reference the grounder can use to identify this lazy clause
	LazyGrounder* monitor; // To request additional grounding
	bool waseq; // True if the lazy Tseitin represents both directions of the equivalence
	Implication implone; // Represents head => body
	Implication impltwo; // Represents ~head => ~body Impltwo is irrelevant if waseq is false.

	litlist newgrounding; // Allows to temporarily store the newly grounded literals

	bool alreadypropagating; // To prevent recursion

public:
	LazyTseitinClause(uint id, PCSolver* engine, const Implication& impl, LazyGrounder* monitor, int clauseID);

	void addGrounding(const litlist& list);

	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause getExplanation(const Lit&) { MAssert(false); return nullPtrClause;}
	virtual void notifyNewDecisionLevel() { MAssert(false); }
	virtual void notifyBacktrack(int, const Lit&){ MAssert(false); }
	virtual int getNbOfFormulas() const { return 1; } // TODO incorrect

private:
	bool checkPropagation(Implication& tocheck, bool signswapped, Implication& complement);
};
}

#endif /* LAZYGROUNDER_HPP_ */
