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

class LazyResidualWatch: public GenWatch{
private:
	PCSolver* engine;
	LazyGroundingCommand* monitor;
	Lit residual;

public:
	LazyResidualWatch(PCSolver* engine, const Lit& lit, LazyGroundingCommand* monitor);

	virtual void propagate();
	virtual const Lit& getPropLit() const;
	virtual bool dynamic() const { return true; }

	friend class LazyResidual;
};

class LazyResidual: public Propagator{
private:
	LazyGroundingCommand* monitor;
	Lit residual;

public:
	LazyResidual(PCSolver* engine, Atom var, LazyGroundingCommand* monitor);
	LazyResidual(LazyResidualWatch* const watch);

	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual rClause getExplanation(const Lit&) { MAssert(false); return nullPtrClause;}
	virtual void notifyNewDecisionLevel() { MAssert(false); }
	virtual void notifyBacktrack(int, const Lit&){ MAssert(false); }
	virtual int getNbOfFormulas() const { return 1; }
};

class LazyTseitinClause: public Propagator{
private:
	int clauseID;
	LazyGrounder* monitor;
	bool waseq;
	Implication implone, impltwo;

	litlist newgrounding;

	bool alreadypropagating;

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
