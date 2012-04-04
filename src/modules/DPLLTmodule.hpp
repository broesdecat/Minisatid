/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef DPLLTMODULE_HPP_
#define DPLLTMODULE_HPP_

#include "utils/Utils.hpp"
#include "theorysolvers/PCSolver.hpp"

namespace MinisatID {

class ConstraintVisitor;

class Propagator {
private:
	bool present;
	int trailindex; //the index in the trail of next propagation to do.
	bool inqueue; //used by the queueing mechanism to refrain from putting a propagator in the queue

	const std::string name;

protected:
	PCSolver* pcsolver;

public:
	Propagator(PCSolver* s, const std::string& name) :
			present(true), trailindex(0), inqueue(false), name(name), pcsolver(s) {
		pcsolver->accept(this);
	}
	virtual ~Propagator() {
	}

	// queueing mech, only use for MAIN (propagation) queue
	void notifyQueued() {
		inqueue = true;
	}
	void notifyDeQueued() {
		inqueue = false;
	}
	bool isQueued() const {
		return inqueue;
	}

	// presence
	bool isPresent() const {
		return present;
	}
	void notifyNotPresent() {
		present = false;
	}

	// Propagator methods
	std::string getName() const{
		return name;
	}
	virtual rClause getExplanation(const Lit&) = 0;
	virtual void accept(ConstraintVisitor& visitor) = 0;
	virtual void notifyNewDecisionLevel() = 0;
	virtual void notifyBacktrack(int untillevel, const Lit& decision); // NOTE: call explicitly when using hasnextprop/nextprop!
	virtual rClause notifypropagate() = 0;
	virtual rClause notifyFullAssignmentFound(){ throw idpexception("Operation applied to invalid propagator."); }

	// Convenience methods (based on getPCSolver)
	const PCSolver& getPCSolver() const {
		return *pcsolver;
	}
	PCSolver& getPCSolver() {
		return *pcsolver;
	}
	const SolverOption& modes() const {
		return getPCSolver().modes();
	}
	int verbosity() const {
		return getPCSolver().verbosity();
	}
	std::string toString(Var atom) const;
	std::string toString(const Lit& lit) const;
	std::string toString(const Lit& lit, lbool value) const;
	bool isTrue(const Lit& l) const {
		return value(l) == l_True;
	}
	bool isFalse(const Lit& l) const {
		return value(l) == l_False;
	}
	bool isUnknown(const Lit& l) const {
		return value(l) == l_Undef;
	}
	lbool value(Var x) const {
		return getPCSolver().value(x);
	}
	lbool value(const Lit& p) const {
		return getPCSolver().value(p);
	}

protected:
	bool hasNextProp();
	const Lit& getNextProp();

	int nVars() const {
		return getPCSolver().nVars();
	}

	void addWatch(Var atom);
	void addWatch(const Lit& lit);
};

}

#endif /* DPLLTMODULE_HPP_ */
