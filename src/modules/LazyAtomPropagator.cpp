/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/LazyAtomPropagator.hpp"
#include <iostream>
#include "utils/Print.hpp"

using namespace MinisatID;
using namespace std;

LazyAtomPropagator::LazyAtomPropagator(PCSolver* engine, const Lit& head, const std::vector<IntView*> args, LazyAtomGrounder* grounder)
		: 	Propagator(engine, "lazy element constraint"),
			head(head),
			args(args),
			grounder(grounder),
			maxsize(0) {

	// TODO overflow checks
	Weight size = 2;
	for (auto arg : args) {
		size *= (arg->origMaxValue() - arg->origMinValue()) + 1;
	}
	if (size > Weight(getMaxElem<int>())) {
		maxsize = getMaxElem<int>();
	} else {
		maxsize = (int) size;
	}
	MAssert(maxsize>=0);

	addPartialChecks(this, args, head);

	getPCSolver().accept(this);
	getPCSolver().accept(this, getHead(), FAST);
	getPCSolver().accept(this, not getHead(), FAST);
	for (auto v : args) {
		getPCSolver().acceptBounds(v, this);
	}
}

void LazyAtomPropagator::accept(ConstraintVisitor&) {
	throw notYetImplemented("From lazy atom propagator to constraints.");
}

rClause LazyAtomPropagator::notifypropagate() {
	auto confl = nullPtrClause;
	auto headvalue = getPCSolver().value(getHead());
	if (headvalue == l_Undef) {
		return confl;
	}
	std::vector<int> argvalues;
	for (auto v : args) {
		//if (grounder->isFunction() && argvalues.size() == args.size() - 1) { // Note: do not need the range to be set for the function
		//	break;
		//}
		if (not v->isKnown()) {
			return confl;
		} else {
			argvalues.push_back((int)v->minValue()); // TODO overflow check
		}
	}
	//if(grounder->isFunction()){
	//	MAssert(argvalues.size() == args.size() - 1);
	//}
	auto fullinst = argvalues;
	fullinst.push_back(headvalue == l_True); // Bit of a hack
	auto exists = grounded.find(fullinst);
	if (exists == grounded.cend()) {
		grounded.insert(fullinst);
		if (maxsize < getMaxElem<int>() && grounded.size() >= (uint) maxsize) {
			notifyNotPresent();
		}
		grounder->ground(headvalue == l_True, argvalues);
	}
	if (getPCSolver().isUnsat()) {
		confl = getPCSolver().createClause(Disjunction({ }), true);
	}
	return confl;
}

int LazyAtomPropagator::getNbOfFormulas() const {
	return maxsize;
}
