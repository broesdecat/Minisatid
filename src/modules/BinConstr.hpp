/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#ifndef BINCONSTR_HPP
#define BINCONSTR_HPP
#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

/**
 * head EQUIV left =< right
 */
class BinaryConstraint: public Propagator {
private:
	Lit head_;
	IntView *left_, *right_;

	struct BinReason {
		IntView* var;
		bool geq;
		int bound;

		BinReason(): var(NULL), geq(false), bound(0){}
		BinReason(IntView* var, bool geq, int bound)
				: var(var), geq(geq), bound(bound) {
		}
	};
	std::map<Lit, BinReason> reasons; // Maps a literal to the propagated intvar (NULL if head) and to the one value necessary for explaining it.

public:
	BinaryConstraint(PCSolver* engine, IntVar* left, EqType comp, IntVar* right, Var h);

	const Lit& head() const {
		return head_;
	}

	// Propagator methods
	virtual rClause getExplanation(const Lit& lit);
	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual int getNbOfFormulas() const {
		return (abs(leftmax() - leftmin())) + (abs(rightmax() - rightmin())) / 2;
	}
	virtual void notifyNewDecisionLevel() {
		throw idpexception("Invalid code path.");
	}
	virtual void notifyBacktrack(int, const Lit&) {
		throw idpexception("Invalid code path.");
	}

	IntView* left() const {
		return left_;
	}
	IntView* right() const {
		return right_;
	}

	int leftmin() const {
		return left_->minValue();
	}
	int leftmax() const {
		return left_->maxValue();
	}
	int rightmin() const {
		return right_->minValue();
	}
	int rightmax() const {
		return right_->maxValue();
	}
};

}

#endif //BINCONSTR_HPP
