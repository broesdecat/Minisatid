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

IntVar::IntVar(PCSolver* solver, int _origid)
		: 	Propagator(solver, "intvar"),
			id_(maxid_++),
			origid_(_origid),
			engine_(*solver) {
}

BasicIntVar::BasicIntVar(PCSolver* solver, int _origid)
		: 	IntVar(solver, _origid) {
}

void IntVar::notifyBacktrack(int, const Lit&) {
	updateBounds();
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

void IntVar::addConstraint(IntVarValue const * const prev, const IntVarValue& lv, IntVarValue const * const next) {
	// leq[i] => leq[i+1]
	if (next!=NULL) {
		internalAdd(Disjunction( { ~getLEQLit(lv.value), getLEQLit(next->value) }), engine());
	} else if(lv.value==origMaxValue()){
		internalAdd(Disjunction( { getLEQLit(lv.value) }), engine());
	}

	//~leq[i] => ~leq[i-1]
	if (prev!=NULL) {
		internalAdd(Disjunction( { getLEQLit(lv.value), ~getLEQLit(prev->value) }), engine());
	}
}

/**
 * x in [min, max]
 * leq[i] => leq[i+1]
 * ~leq[i] => ~leq[i-1]
 */
void BasicIntVar::addConstraints() {
	for (uint i = 0; i < leqlits.size(); ++i) {
		IntVarValue* next = NULL;
		if(i < leqlits.size() - 1){
			next = &leqlits[i + 1];
		}
		IntVarValue* prev = NULL;
		if(i>0){
			prev = &leqlits[i - 1];
		}
		addConstraint(prev, leqlits[i], next);
	}
}

/**
 * lazy intvar:
 *
 * introduce one variable
 * When it is assigned a value, introduce one within the relevant remaining interval
 * If there are two vars which are consecutive in the full interval and one is false and the other one true, then no more introduction is necessary
 */

void BasicIntVar::updateBounds() {
	for (auto i = leqlits.cbegin(); i < leqlits.cend(); ++i) {
		if (not isFalse(mkPosLit(i->atom))) { // First non-false is lowest remaining value
			currentmin = i->value;
			break;
		}
	}

	bool found = false;
	for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) { // NOTE: reverse iterated!
		if (not isTrue(mkPosLit(i->atom))) { // First non true => previous is highest remaining value (LEQ!)
			currentmax = (--i)->value;
			found = true;
			break;
		}
	}
	if (not found) {
		currentmax = leqlits.front().value;
	}
	MAssert(isTrue(getGEQLit(minValue())));
	MAssert(isTrue(getLEQLit(maxValue())));
//	cerr <<"Updated bounds for var" <<origid() <<" to ["<<minValue() <<"," <<maxValue() <<"]\n";
}

RangeIntVar::RangeIntVar(PCSolver* solver, int _origid, int min, int max)
		: BasicIntVar(solver, _origid) {
	if(min>max){
		getPCSolver().notifyUnsat(); //FIXME not able to explain this atm
		notifyNotPresent(); // FIXME what if the explanation is required later on? => check reason list before deleting
		return;
	}
	setOrigMax(max);
	setOrigMin(min);

	for (int i = origMinValue(); i < origMaxValue() + 1; ++i) {
		auto var = engine().newVar();
		leqlits.push_back(IntVarValue(this, var, i));
		engine().accept(this, mkPosLit(var), FASTEST);
		engine().accept(this, mkNegLit(var), FASTEST);
		if (verbosity() > 3) {
			clog << toString(mkPosLit(var)) << " <=> " << "var" << origid() << "=<" << i << "\n";
		}
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().acceptBounds(new IntView(this, 0), this);

	addConstraints();

	engine().notifyBoundsChanged(this);
}

Lit RangeIntVar::getLEQLit(int bound) {
//	cerr <<"Requesting var" <<origid() <<"[" <<origMinValue() <<"," <<origMaxValue() <<"]" <<"=<" <<bound <<"\n";
	auto index = bound - origMinValue();
	if (index < 0) {
		return getPCSolver().getFalseLit();
	}
	if ((int) leqlits.size() <= index) {
		return getPCSolver().getTrueLit();
	}
	return mkPosLit(leqlits[index].atom);
}

Lit RangeIntVar::getGEQLit(int bound) {
	return not getLEQLit(bound-1);
}

EnumIntVar::EnumIntVar(PCSolver* solver, int _origid, const std::vector<int>& values)
		: 	BasicIntVar(solver, _origid),
			_values(values) {
	if(values.empty()){
		getPCSolver().notifyUnsat(); //FIXME not able to explain this atm
		notifyNotPresent();
		return;
	}
	sort(_values.begin(), _values.end());
	setOrigMin(values.front());
	setOrigMax(values.back());

	for (auto i = values.cbegin(); i < values.cend(); ++i) {
		auto var = engine().newVar();
		leqlits.push_back(IntVarValue(this, var, *i));
		engine().accept(this, mkPosLit(var), FASTEST);
		engine().accept(this, mkNegLit(var), FASTEST);
		if (verbosity() > 3) {
			clog << toString(mkPosLit(var)) << " <=> " << "var" << origid() << "=<" << *i << "\n";
		}
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().acceptBounds(new IntView(this, 0), this);

	addConstraints();

	engine().notifyBoundsChanged(this);
}

Lit EnumIntVar::getLEQLit(int bound) {
//	cerr <<"Requesting var" <<origid() <<"{" <<origMinValue() <<",()," <<origMaxValue() <<"}" <<">=" <<bound <<"\n";
	if (origMaxValue() < bound) {
		return getPCSolver().getTrueLit();
	} else if (bound < origMinValue()) {
		return getPCSolver().getFalseLit();
	} else {
		for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) {
			if (i->value <= bound) {
				return mkPosLit(i->atom);
			}
		}
		throw idpexception("Invalid code path");
	}
}

Lit EnumIntVar::getGEQLit(int bound) {
//	cerr <<"Requesting var" <<origid() <<"{" <<origMinValue() <<",()," <<origMaxValue() <<"}" <<">=" <<bound <<"\n";
	if (bound <= origMinValue()) {
		return getPCSolver().getTrueLit();
	} else if (origMaxValue() < bound) {
		return getPCSolver().getFalseLit();
	} else {
		for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) {
			if (i->value < bound) {
				return mkNegLit(i->atom);
			} else if (bound == i->value) {
				return mkNegLit((++i)->atom);
			}
		}
		throw idpexception("Invalid code path");
	}
}
