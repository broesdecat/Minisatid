/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#pragma once

#include "modules/IntVar.hpp"
#include "modules/DPLLTmodule.hpp"

namespace MinisatID {

class PropagatorFactory;

/**
 * head EQUIV left =< right
 */
class BinaryConstraint: public Propagator {
private:
	Lit head_;
	IntView *left_, *right_;

	struct BinReason {
		bool left;
		bool geq;
		Weight bound, rightbound; // first is leftbound is headreason, otherwise second bound is irrelevant

		BinReason(): left(false), geq(false), bound(0), rightbound(0){}
		BinReason(bool left, bool geq, Weight bound, Weight rightbound = 0)
				: left(left), geq(geq), bound(bound), rightbound(rightbound) {
		}
	};
	std::map<Lit, BinReason> reasons; // Maps a literal to the propagated intvar (NULL if head) and to the one value necessary for explaining it.

	friend class PropagatorFactory;
	BinaryConstraint(PCSolver* engine, IntView* left, EqType comp, IntView* right, const Lit& h);

public:
	const Lit& head() const {
		return head_;
	}

	// Propagator methods
	virtual rClause getExplanation(const Lit& lit);
	virtual rClause notifypropagate();
	virtual void accept(ConstraintVisitor& visitor);
	virtual int getNbOfFormulas() const;
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

	Weight leftmin() const {
		return left_->minValue();
	}
	Weight leftmax() const {
		return left_->maxValue();
	}
	Weight rightmin() const {
		return right_->minValue();
	}
	Weight rightmax() const {
		return right_->maxValue();
	}
};

}
