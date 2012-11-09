/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/LazyGrounder.hpp"
#include <iostream>
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace std;
using namespace MinisatID;

// Watch BOTH: so watching when it becomes decidable
LazyResidual::LazyResidual(PCSolver* engine, Atom var, Value watchedvalue, LazyGroundingCommand* monitor)
		: 	Propagator(DEFAULTCONSTRID, engine, "lazy residual notifier"),
			monitor(monitor),
			residual(var),
			watchedvalue(watchedvalue) {
	getPCSolver().accept(this);
	switch (watchedvalue) {
	case Value::True:
		getPCSolver().accept(this, mkPosLit(var), PRIORITY::FAST);
		break;
	case Value::False:
		getPCSolver().accept(this, mkNegLit(var), PRIORITY::FAST);
		break;
	case Value::Unknown:
		getPCSolver().acceptForDecidable(var, this);
		break;
	}
}

void LazyResidual::accept(ConstraintVisitor& visitor) {
	visitor.add(LazyGroundLit(residual, watchedvalue, monitor));
}

rClause LazyResidual::notifypropagate() {
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	// NOTE: have to make sure that constraints are never added at a level where they will no have full effect!

	auto confl = nullPtrClause;
	switch (watchedvalue) {
	case Value::Unknown:
		if (not getPCSolver().isDecisionVar(residual)) {
			return confl;
		}
		break;
	case Value::False:
		if (getPCSolver().value(mkPosLit(residual)) != l_False) {
			return confl;
		}
		break;
	case Value::True:
		if (getPCSolver().value(mkPosLit(residual)) != l_True) {
			return confl;
		}
		break;
	}
	//cerr <<"Firing " <<toString(residual) <<" for watched value " <<watchedvalue <<" with value " <<truthvalue <<"\n";
	monitor->requestGrounding(watchedvalue);

	if (not getPCSolver().isUnsat()) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().finishParsing(); // FIXME each time?
	}
	notifyNotPresent();

	if (getPCSolver().isUnsat()) {
		confl = getPCSolver().createClause(Disjunction(DEFAULTCONSTRID, { }), true);
	}
	return confl;
}

LazyTseitinClause::LazyTseitinClause(uint id, PCSolver* engine, const Implication& impl, LazyGrounder* monitor, int clauseID)
		: 	Propagator(id, engine, "lazy tseitin eq"),
			clauseID(clauseID),
			monitor(monitor),
			type(impl.type),
			implone(impl),
			impltwo(impl),
			alreadypropagating(false) {
	if (hasImplies()) {
		implone = Implication(getID(), impl.head, ImplicationType::IMPLIES, impl.body, impl.conjunction);
	}
	if (hasImpliedBy()) {
		litlist lits;
		for (auto i = impl.body.cbegin(); i < impl.body.cend(); ++i) {
			lits.push_back(not *i);
		}
		impltwo = Implication(getID(), not impl.head, ImplicationType::IMPLIES, lits, not impl.conjunction);
	}

	if (hasImplies() && implone.conjunction) {
		for (auto i = implone.body.cbegin(); i < implone.body.cend(); ++i) {
			add(Disjunction(getID(), { not implone.head, *i }));
		}
		implone.body.clear(); // Clear all current literals. Only when more are added do we need to consider this
	}
	if (hasImpliedBy() && impltwo.conjunction) {
		for (auto i = impltwo.body.cbegin(); i < impltwo.body.cend(); ++i) {
			add(Disjunction(getID(), { not impltwo.head, *i }));
		}
		impltwo.body.clear(); // Clear all current literals. Only when more are added do we need to consider this
	}

	getPCSolver().accept(this);
	getPCSolver().acceptForPropagation(this);
}

void LazyTseitinClause::accept(ConstraintVisitor&) {
	notYetImplemented("Accepting lazily grounded Tseitin equivalences.");
}

class BasicPropWatch: public GenWatch {
private:
	Lit watch;
	Propagator* p;
public:
	BasicPropWatch(const Lit& watch, Propagator* p)
			: 	watch(watch),
				p(p) {
	}

	virtual void propagate() {
		p->getPCSolver().acceptForPropagation(p);
	}
	virtual const Lit& getPropLit() const {
		return watch;
	}
	virtual bool dynamic() const {
		return true;
	}
};

/**
 * This class can represent a lazily ground implication or equivalence
 * Depending on the type, propagation can be guaranteed:
 *
 * head => L1 | ... | Ln | T (T is the implicit Tseitin representing a lazily ground formula)
 * 		watch 2 non-false literals. When only one left, ground more.
 * 			Guarantees propagation
 * head => L1 & ... & Ln & T
 * 		add clauses head => Li
 * 		watch head
 * 			if head true, ground T => possible heuristic derived from this: set head polarity to false
 * 			=> loss of propagation from T (if false) to head
 *
 * 	If eq, combine both
 */
rClause LazyTseitinClause::notifypropagate() {
	if (alreadypropagating) {
		return nullPtrClause;
	}
	alreadypropagating = true;
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	bool groundedall = false;
	if (hasImpliedBy()) {
		groundedall = checkPropagation(impltwo, true, implone);
	}
	if (not groundedall && hasImplies()) {
		groundedall = checkPropagation(implone, false, impltwo);
	}

	if (not getPCSolver().isUnsat()) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().notifyFinishParsingNeed();
	}

	if (groundedall) {
		notifyNotPresent(); // IMPORTANT: only do this after finishparsing as this propagator is then DELETED
	}

	auto confl = nullPtrClause;
	if (getPCSolver().isUnsat()) {
		confl = getPCSolver().createClause(Disjunction(DEFAULTCONSTRID, { }), true);
	}
	alreadypropagating = false;
	return confl;
}

void LazyTseitinClause::addGrounding(const litlist& list) {
	newgrounding = list;
}

bool LazyTseitinClause::checkPropagation(Implication& tocheck, bool signswapped, Implication& complement) {
	bool groundedall = false;
	if (tocheck.conjunction) {
		if (value(tocheck.head) == l_True) {
			groundedall = true;
			bool stilldelayed = true;
			monitor->requestGrounding(clauseID, true, stilldelayed); // get all grounding
			for (auto bdl : newgrounding) {
				add(Disjunction(getID(), { not tocheck.head, signswapped ? not bdl : bdl }));
				if (isEquivalence()) {
					complement.body.push_back(signswapped ? bdl : not bdl);
				}
			}
			if(isEquivalence()) {
				auto lits = complement.body;
				lits.push_back(not complement.head);
				add(Disjunction(getID(), lits));
			}
		} else { // Can only happen once, at initialization (if the head has not yet become true at any point). If it becomes true, it is grounded and removed
			getPCSolver().accept(new BasicPropWatch(tocheck.head, this));
		}
	} else {
		uint nonfalse = 0;
		uint index = 0;
		if (value(tocheck.head) != l_True) { // Remember, IMPLICATION!
			nonfalse++;
			getPCSolver().accept(new BasicPropWatch(tocheck.head, this));
		}
		while (nonfalse < 1) { // NOTE 1 or 2 in this condition is the difference between one-watched or two-watched schema!
			MAssert(tocheck.body.size()+1>=index);
			if (tocheck.body.size() <= index) {
				bool stilldelayed = true;
				newgrounding.clear();
				monitor->requestGrounding(clauseID, false, stilldelayed);
				if (not stilldelayed) {
					groundedall = true;
					if (newgrounding.empty()) {
						break;
					}
				}
				MAssert(not newgrounding.empty());
				for (auto bdl : newgrounding) {
					tocheck.body.push_back(signswapped ? not bdl : bdl);
				}
				if (isEquivalence()) {
					for (auto bdl : newgrounding) {
						add(Disjunction(getID(), { not complement.head, signswapped ? bdl : not bdl }));
					}
				}
			}
			if (groundedall) {
				break;
			}
			MAssert(tocheck.body.size()>index);
			if (value(tocheck.body[index]) != l_False) {
				if (index != nonfalse) {
					auto temp = tocheck.body[nonfalse];
					tocheck.body[nonfalse] = tocheck.body[index];
					tocheck.body[index] = temp;
				}
				getPCSolver().accept(new BasicPropWatch(not tocheck.body[nonfalse], this));
				nonfalse++;
			}
			index++;
		}
		if (groundedall) {
			if (tocheck.conjunction) {
				MAssert(false);
			} else {
				auto lits = tocheck.body;
				lits.push_back(not tocheck.head);
				add(Disjunction(getID(), lits));
			}
		}
	}
	return groundedall;
}
