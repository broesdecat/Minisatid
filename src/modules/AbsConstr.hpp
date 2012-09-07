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

// TODO implement exactly the same for min, max and modulo
/**
 * Consistency propagator for expressions "head EQUIV abs(left)=right"
 */
class AbsConstraint: public Propagator {
private:
	Lit head_;
	IntView *left_, *right_;

public:
	AbsConstraint(PCSolver* engine, Atom head, IntVar* left, IntVar* right);

	const Lit& head() const {
		return head_;
	}

	// Propagator methods
	virtual rClause getExplanation(const Lit& lit){
		throw idpexception("Invalid code path.");
	}
	virtual rClause notifypropagate(){
		auto headvalue = value(head());
		if(not left()->isKnown() || not right()->isKnown() || not headvalue!=l_Undef){
			// TODO smarter than consistency check
			return nullPtrClause;
		}
		auto confl = nullPtrClause;
		auto leftval = left()->minValue();
		auto rightval = right()->minValue();
		if(headvalue==l_True && abs(leftval)!=rightval){
			// head & left==leftval IMPLIES right=abs(leftval)
			auto confl = getPCSolver().createClause(Disjunction({~head(), ~left()->getEQLit(leftval), right()->getEQLit(abs(leftval))}), true);
			getPCSolver().addConflictClause(confl);
		}else if(headvalue==l_False && abs(leftval)==rightval){
			// NOT head AND left==leftval IMPLIES right~=abs(leftval)
			auto confl = getPCSolver().createClause(Disjunction({head(), ~left()->getEQLit(leftval), ~right()->getEQLit(abs(leftval))}), true);
			getPCSolver().addConflictClause(confl);
		}
		return confl;
	}
	virtual void accept(ConstraintVisitor& visitor){}
	virtual int getNbOfFormulas() const {
		return 1; // TODO
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
};

}

#endif //BINCONSTR_HPP
