/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/LazyImplication.hpp"
#include <iostream>
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace std;
using namespace MinisatID;

class BasicPropWatch: public GenWatch {
private:
	Lit watch;
	bool implies;
	LazyTseitinClause* p;
public:
	BasicPropWatch(const Lit& watch, LazyTseitinClause* p, bool implies)
			: 	watch(watch),
				implies(implies),
				p(p) {
	}

	virtual void propagate() {
		if (p->verbosity() > 7) {
			clog << "Firing lazy watch " << p->toString(watch) << "\n";
		}
		p->fired(implies);
		p->getPCSolver().acceptForPropagation(p);
	}
	virtual const Lit& getPropLit() const {
		return watch;
	}
	virtual bool dynamic() const {
		return true;
	}
};

int LazyTseitinClause::ltcids = 0;
LazyTseitinClause::LazyTseitinClause(PCSolver* engine, const Implication& impl, LazyGrounder* monitor, int clauseID)
		: 	Propagator(engine, "lazy tseitin eq"),
			ltcid(ltcids++),
			clauseID(clauseID),
			monitor(monitor),
			type(impl.type),
			implone(impl),
			impltwo(impl),
			alreadypropagating(false),
			impliesfired(false),
			impliedbyfired(false) {
	if (hasImplies()) {
		implone = Implication(impl.head, ImplicationType::IMPLIES, impl.body, impl.conjunction);
	}
	if (hasImpliedBy()) {
		litlist lits;
		for (auto i = impl.body.cbegin(); i < impl.body.cend(); ++i) {
			lits.push_back(not *i);
		}
		impltwo = Implication(not impl.head, ImplicationType::IMPLIES, lits, not impl.conjunction);
	}

	if (hasImplies() && implone.conjunction) {
		for (auto i = implone.body.cbegin(); i < implone.body.cend(); ++i) {
			add(Disjunction({ not implone.head, *i }));
		}
		implone.body.clear(); // Clear all current literals. Only when more are added do we need to consider this
	}
	if (hasImpliedBy() && impltwo.conjunction) {
		for (auto i = impltwo.body.cbegin(); i < impltwo.body.cend(); ++i) {
			add(Disjunction({ not impltwo.head, *i }));
		}
		impltwo.body.clear(); // Clear all current literals. Only when more are added do we need to consider this
	}

	impliesfired = hasImplies();
	impliedbyfired = hasImpliedBy();

	getPCSolver().accept(this);
	getPCSolver().acceptForPropagation(this);
}

void LazyTseitinClause::accept(ConstraintVisitor&) {
	notYetImplemented("Accepting lazily grounded Tseitin equivalences.");
}

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

	bool groundedall = false;
	bool grounded = false;
	while (not groundedall && (impliesfired || impliedbyfired)) {
		if (hasImpliedBy() && impliedbyfired) {
			groundedall = checkPropagation(impltwo, true, implone, grounded);
			impliedbyfired = false;
		}
		if (not groundedall && hasImplies() && impliesfired) {
			groundedall = checkPropagation(implone, false, impltwo, grounded);
			impliesfired = false;
		}
	}

	if (grounded) {
		getPCSolver().notifyFinishParsingNeed();

		if (groundedall) {
			notifyNotPresent(); // IMPORTANT: only do this after notifyFinishParsingNeed as finishparsing deletes not-present propagators!
		}
	}

	alreadypropagating = false;

	auto confl = nullPtrClause;
	if (getPCSolver().isUnsat()) {
		confl = getPCSolver().createClause(Disjunction({ }), true);
	}
	return confl;
}

void LazyTseitinClause::addGrounding(const litlist& list) {
	newgrounding = list;
}

// Returns true iff no more grounding is available for this clause
bool LazyTseitinClause::checkPropagation(Implication& tocheck, bool impliedby, Implication& complement, bool& grounded) {
	bool groundedall = false;
	if (tocheck.conjunction) { // TODO what if groundall is very large and restarting might help out?
		if (value(tocheck.head) == l_True) {
			getPCSolver().notifyGroundingCall();
		}else if (not getPCSolver().modes().expandimmediately){
			getPCSolver().accept(new BasicPropWatch(tocheck.head, this, not impliedby));
			return false;
		}
		// Head true in conjunction => ground all
		bool stilldelayed = true;
		grounded = true;
		groundedall = true;
		monitor->requestGrounding(clauseID, true, stilldelayed); // get all grounding
		for (auto bdl : newgrounding) {
			add(Disjunction({ not tocheck.head, impliedby ? not bdl : bdl }));
			if (isEquivalence()) {
				complement.body.push_back(impliedby ? bdl : not bdl);
			}
		}
		if (isEquivalence()) {
			auto lits = complement.body;
			lits.push_back(not complement.head);
			add(Disjunction(lits));
		}
	} else {
		uint nonfalse = 0;
		uint index = 0;
		if (value(tocheck.head) != l_True) { // Remember, IMPLICATION!
			nonfalse++;
			getPCSolver().accept(new BasicPropWatch(tocheck.head, this, not impliedby));
		}
		while (getPCSolver().modes().expandimmediately || nonfalse < 1) { // NOTE 1 or 2 in this condition is the difference between one-watched or two-watched schema!
			MAssert(tocheck.body.size() + 1 >= index);
			if (tocheck.body.size() <= index) {
				getPCSolver().notifyGroundingCall();
				bool stilldelayed = true;
				newgrounding.clear();
				grounded = true;
				monitor->requestGrounding(clauseID, false, stilldelayed);
				if (not stilldelayed) {
					groundedall = true;
					if (newgrounding.empty()) {
						break;
					}
				}
				MAssert(not newgrounding.empty());
				for (auto bdl : newgrounding) {
					tocheck.body.push_back(impliedby ? not bdl : bdl);
				}
				if (isEquivalence()) {
					for (auto bdl : newgrounding) {
						add(Disjunction({ not complement.head, impliedby ? bdl : not bdl }));
					}
				}
			}
			if (groundedall) {
				break;
			}
			MAssert(tocheck.body.size() > index);
			if (not modes().expandimmediately && value(tocheck.body[index]) != l_False) {
				if (index != nonfalse) {
					auto temp = tocheck.body[nonfalse];
					tocheck.body[nonfalse] = tocheck.body[index];
					tocheck.body[index] = temp;
				}
				getPCSolver().accept(new BasicPropWatch(not tocheck.body[nonfalse], this, not impliedby));
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
				add(Disjunction(lits));
			}
		}
	}
	if (modes().expandimmediately && not groundedall) {
		throw idpexception("Invalid code path: did not ground all in immediate expansion mode.");
	}
	return groundedall;
}
