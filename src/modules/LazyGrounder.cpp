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

LazyResidualWatch::LazyResidualWatch(PCSolver* engine, const Lit& lit, LazyGroundingCommand* monitor)
		: 	engine(engine),
			monitor(monitor),
			residual(lit) {
	engine->accept(this);
}

void LazyResidualWatch::propagate() {
	new LazyResidual(this);
}

const Lit& LazyResidualWatch::getPropLit() const {
	return residual;
}

// Watch BOTH: so watching when it becomes decidable
LazyResidual::LazyResidual(PCSolver* engine, Var var, LazyGroundingCommand* monitor)
		: 	Propagator(engine, "lazy residual notifier"),
			monitor(monitor),
			residual(mkPosLit(var)) {
	getPCSolver().accept(this);
	getPCSolver().acceptForDecidable(var, this);
}

LazyResidual::LazyResidual(LazyResidualWatch* const watch)
		: 	Propagator(watch->engine, "lazy residual notifier"),
			monitor(watch->monitor),
			residual(watch->residual) {
	getPCSolver().accept(this);
	getPCSolver().acceptForPropagation(this);
}

void LazyResidual::accept(ConstraintVisitor& visitor) {
	visitor.add(LazyGroundLit(false, residual, monitor));
}

rClause LazyResidual::notifypropagate() {
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	// NOTE: have to make sure that constraints are never added at a level where they will no have full effect!

	// TODO check whether preventprop is still necessary
//	getPCSolver().preventPropagation(); // NOTE: necessary for inductive definitions, as otherwise might try propagation before all rules for some head have been added.
	monitor->requestGrounding(); // FIXME should delete the other watch too
//	getPCSolver().allowPropagation();

	if (not getPCSolver().isUnsat() /* FIXME FIXME && getPCSolver().isInitialized()*/) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().finishParsing();
	}
	notifyNotPresent(); // FIXME clean way of deleting this? FIXME only do this after finishparsing as this propagated is then DELETED

	if (getPCSolver().isUnsat()) {
		return getPCSolver().createClause( { }, true);
	} else {
		return nullPtrClause;
	}
}

LazyTseitinClause::LazyTseitinClause(PCSolver* engine, Implication impl, LazyGrounder* monitor)
		: 	Propagator(engine, "lazy tseitin eq"),
			monitor(monitor),
			waseq(impl.type == ImplicationType::EQUIVALENT),
			implone(impl),
			impltwo(impl) {
	if (waseq) {
		implone = Implication(impl.head, ImplicationType::IMPLIES, impl.body, impl.conjunction);
		litlist lits;
		for (auto i = impl.body.cbegin(); i < impl.body.cend(); ++i) {
			lits.push_back(not *i);
		}
		impltwo = Implication(not impl.head, ImplicationType::IMPLIES, lits, not impl.conjunction);
	} else {
		implone = impl;
	}

	if (implone.conjunction) {
		for (auto i = implone.body.cbegin(); i < implone.body.cend(); ++i) {
			internalAdd(Disjunction( { not implone.head, *i }), *engine);
		}
		implone.body.clear();
	}
	if (waseq && impltwo.conjunction) {
		for (auto i = impltwo.body.cbegin(); i < impltwo.body.cend(); ++i) {
			internalAdd(Disjunction( { not impltwo.head, *i }), *engine);
		}
		impltwo.body.clear();
	}

	getPCSolver().accept(this);
	getPCSolver().acceptForPropagation(this);
}

void LazyTseitinClause::accept(ConstraintVisitor& visitor) {
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
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	bool groundedall = false;
	if (waseq) {
		groundedall = checkPropagation(impltwo, implone);
	}
	if (not groundedall) {
		groundedall = checkPropagation(implone, impltwo);
	}

	if (not getPCSolver().isUnsat()) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().finishParsing();
	}

	if (groundedall) {
		notifyNotPresent(); // IMPORTANT/ only do this after finishparsing as this propagator is then DELETED
	}

	if (getPCSolver().isUnsat()) {
		return getPCSolver().createClause(Disjunction(), true);
	} else {
		return nullPtrClause;
	}
}

void LazyTseitinClause::addGrounding(const litlist& list){
	newgrounding = list;
}

bool LazyTseitinClause::checkPropagation(Implication& tocheck, Implication& complement) {
	bool groundedall = false;
	if (tocheck.conjunction) {
		if (value(tocheck.head) == l_True) {
			groundedall = true;
			bool stilldelayed = true;
			monitor->requestGrounding(true, stilldelayed); // get all grounding
			for (auto i = newgrounding.cbegin(); i < newgrounding.cend(); ++i) {
				internalAdd(Disjunction( { not tocheck.head, *i }), getPCSolver());
				if (waseq) {
					complement.body.push_back(~*i);
				}
			}
			internalAdd(Disjunction(complement.body), getPCSolver());
		} else { // Can only happen once, at initialization
			getPCSolver().accept(new BasicPropWatch(tocheck.head, this));
		}
	} else {
		int nonfalse = 0;
		int index = 0;
		while (nonfalse < 2) {
			MAssert(implone.body.size()+1>=index);
			if (tocheck.body.size() <= index) {
				bool stilldelayed = true;
				monitor->requestGrounding(false, stilldelayed);
				if (stilldelayed) {
					groundedall = true;
					break;
				}
				tocheck.body.insert(tocheck.body.end(), newgrounding.cbegin(), newgrounding.cend());
				for (auto i = newgrounding.cbegin(); i < newgrounding.cend(); ++i) {
					internalAdd(Disjunction( { not tocheck.head, ~*i }), getPCSolver());
				}
			}
			if (value(tocheck.body[index]) != l_False) {
				if (index != nonfalse) {
					auto temp = tocheck.body[nonfalse];
					tocheck.body[nonfalse] = tocheck.body[index];
					tocheck.body[index] = temp;
					getPCSolver().accept(new BasicPropWatch(tocheck.body[nonfalse], this));
				}
				nonfalse++;
			}
			index++;
		}
	}
	return groundedall;
}
