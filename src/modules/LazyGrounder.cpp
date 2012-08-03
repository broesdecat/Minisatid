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
		: engine(engine), monitor(monitor), residual(lit) {
	engine->accept(this);
}

void LazyResidualWatch::propagate() {
	new LazyResidual(this);
}

const Lit& LazyResidualWatch::getPropLit() const {
	return residual;
}

// Watch BOTH: so watching when it becomes decidable
LazyResidual::LazyResidual(PCSolver* engine, Atom var, LazyGroundingCommand* monitor)
		: Propagator(engine, "lazy residual notifier"), monitor(monitor), residual(mkPosLit(var)) {
	getPCSolver().accept(this);
	getPCSolver().acceptForDecidable(var, this);
}

LazyResidual::LazyResidual(LazyResidualWatch* const watch)
		: Propagator(watch->engine, "lazy residual notifier"), monitor(watch->monitor), residual(watch->residual) {
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

	auto val = getPCSolver().value(residual);
	auto truthvalue = Value::Unknown;
	if (val == l_True) {
		truthvalue = Value::True;
	} else if (val == l_False) {
		truthvalue = Value::False;
	}
	monitor->requestGrounding(truthvalue);

	if (not getPCSolver().isUnsat()) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().finishParsing();
	}
	notifyNotPresent();

	if (getPCSolver().isUnsat()) {
		return getPCSolver().createClause( { }, true);
	} else {
		return nullPtrClause;
	}
}

LazyTseitinClause::LazyTseitinClause(PCSolver* engine, Implication impl, LazyGrounder* monitor, int ID)
		: Propagator(engine, "lazy tseitin eq"), id(ID), monitor(monitor), waseq(impl.type == ImplicationType::EQUIVALENT), implone(impl), impltwo(impl),
			alreadypropagating(false) {
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
			: watch(watch), p(p) {
		//cerr <<"Watching " <<toString(watch, p->getPCSolver()) <<" in lazy propagator.\n";
	}

	virtual void propagate() {
		//cerr <<"Accepted for propagation on " <<toString(watch, p->getPCSolver()) <<"\n";
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
	//cerr <<"Propagating " <<long(this) <<"\n";
	MAssert(isPresent());
	MAssert(not getPCSolver().isUnsat());

	bool groundedall = false;
	if (waseq) {
		groundedall = checkPropagation(impltwo, true, implone); // NOTE: invar: impltwo is the implication with swapped signs!
	}
	if (not groundedall) {
		groundedall = checkPropagation(implone, false, impltwo);
	}

	if (not getPCSolver().isUnsat()) { // NOTE: otherwise, it will be called later and would be incorrect here!
		getPCSolver().notifyFinishParsingNeed();
	}

	if (groundedall) {
		notifyNotPresent(); // IMPORTANT/ only do this after finishparsing as this propagator is then DELETED
	}

	//cerr <<"Finished propagating " <<long(this) <<"\n";
	auto confl = nullPtrClause;
	if (getPCSolver().isUnsat()) {
		confl = getPCSolver().createClause(Disjunction(), true);
	}
	alreadypropagating = false;
	return confl;
}

void LazyTseitinClause::addGrounding(const litlist& list) {
	//cerr <<"Adding grounding" <<long(this) <<"\n";
	newgrounding = list;
}

bool LazyTseitinClause::checkPropagation(Implication& tocheck, bool signswapped, Implication& complement) {
	bool groundedall = false;
	if (tocheck.conjunction) {
		if (value(tocheck.head) == l_True) {
			groundedall = true;
			bool stilldelayed = true;
			monitor->requestGrounding(id, true, stilldelayed); // get all grounding
			for (auto i = newgrounding.cbegin(); i < newgrounding.cend(); ++i) {
				internalAdd(Disjunction( { not tocheck.head, signswapped ? not *i : *i }), getPCSolver());
				if (waseq) {
					complement.body.push_back(signswapped ? *i : not *i);
				}
			}
			auto lits = complement.body;
			lits.push_back(not complement.head);
			internalAdd(Disjunction(lits), getPCSolver());
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
				monitor->requestGrounding(id, false, stilldelayed);
				if (not stilldelayed) {
					groundedall = true;
					if (newgrounding.empty()) {
						break;
					}
				}
				MAssert(not newgrounding.empty());
				for (auto i = newgrounding.cbegin(); i < newgrounding.cend(); ++i) {
					tocheck.body.push_back(signswapped ? not *i : *i);
				}
				if (waseq) {
					for (auto i = newgrounding.cbegin(); i < newgrounding.cend(); ++i) {
						internalAdd(Disjunction( { not complement.head, signswapped ? *i : not *i }), getPCSolver());
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
			auto lits = tocheck.body;
			lits.push_back(not tocheck.head);
			internalAdd(Disjunction(lits), getPCSolver());
		}
	}
	return groundedall;
}
