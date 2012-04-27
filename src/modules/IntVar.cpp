/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/IntVar.hpp"
#include <iostream>
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace MinisatID;
using namespace std;

// TODO easily adaptable to also support enums of weights
IntVar::IntVar(PCSolver* solver, int _origid, int min, int max)
		: Propagator(solver, "intvar"), id_(maxid_++), origid_(_origid), engine_(*solver), minvalue(min), maxvalue(max), offset(-1), currentmin(min),
			currentmax(max) {
	for (int i = origMinValue(); i < origMaxValue() + 1; ++i) {
		auto var = engine().newVar();
		leqlits.push_back(IntVarValue(this, var, i + minValue()));
	}
	for (auto i = leqlits.cbegin(); i < leqlits.cend(); ++i) {
		engine().accept(this, mkPosLit(i->atom), FAST);
		engine().accept(this, mkNegLit(i->atom), FAST);
	}
	addConstraints();

	if (verbosity() > 3) {
		auto index = 0;
		for (auto i = leqlits.cbegin(); i < leqlits.cend(); ++i, index++) {
			clog << toString(mkPosLit(i->atom)) << " <=> " << "var" << origid() << "=<" << minvalue + index << "\n";
		}
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_PROPAGATE);
	getPCSolver().acceptBounds(new IntView(this, 0), this);
	engine().notifyBoundsChanged(this);
}

void IntVar::updateBounds() {
	for (auto i=leqlits.cbegin(); i<leqlits.cend(); ++i) {
		if (not isFalse(mkPosLit(i->atom))) { // First non-false is lowest remaining value
			currentmin = i->value;
			break;
		}
	}
	for (auto i=leqlits.crbegin(); i<leqlits.crend(); ++i) {
		if (not isTrue(mkPosLit(i->atom))) { // First non true is highest remaining value
			currentmax = i->value;
			break;
		}
	}
}

void IntVar::notifyBacktrack(int, const Lit&) {
	updateBounds();
}

// NOTE: returns false if out of the bounds
Lit IntVar::getLEQLit(int bound) const {
	auto index = bound - minvalue;
	if (index < 0) {
		return getPCSolver().getFalseLit();
	}
	if ((int) leqlits.size() <= index) {
		return getPCSolver().getTrueLit();
	}
	return mkPosLit(leqlits[index].atom);
}

Lit IntVar::getGEQLit(int bound) const {
	auto index = bound - minvalue - 1;
	if (index < 0) {
		return getPCSolver().getTrueLit();
	}
	if ((int) leqlits.size() <= index) {
		return getPCSolver().getFalseLit();
	}
	return mkNegLit(leqlits[index].atom);
}

void IntVar::accept(ConstraintVisitor& visitor) {
	// FIXME
	//		which id to use (what with internal vars)
	//		also add eq and diseq reifs? (can occur in other constraints!)
}

rClause IntVar::notifypropagate() {
	int lastmin = currentmin, lastmax = currentmax;
	updateBounds();
	if (lastmin != currentmin || lastmax != currentmax) {
		if (verbosity() > 7) {
			clog << ">>> After bounds update: var range is " << origid() << "[" << currentmin << "," << currentmax << "]\n";
		}
		engine().notifyBoundsChanged(this);
	}

	return nullPtrClause;
}

/**
 * x in [min, max]
 * some leq is true
 * leq[i] => leq[i+1]
 * ~leq[i] => ~leq[i-1]
 */
void IntVar::addConstraints() {
	Disjunction sometrue;
	for (uint i = 0; i < leqlits.size(); ++i) {
		// leq[i] => leq[i+1]
		internalAdd(Disjunction( { ~getLEQLit(i), getLEQLit(i + 1) }), engine());
		//~leq[i] => ~leq[i-1]
		internalAdd(Disjunction( { getLEQLit(i), ~getLEQLit(i-1)}), engine());
		sometrue.literals.push_back(getLEQLit(i));
	}
	// some leq is true
	internalAdd(sometrue, engine());
}
