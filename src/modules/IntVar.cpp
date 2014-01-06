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

IntVar::IntVar(uint id, PCSolver* solver, VarID varid)
		: Propagator(id, solver, "intvar"), varid_(varid), engine_(*solver), minvalue(0), maxvalue(0), currentmin(0), currentmax(0) {
}

BasicIntVar::BasicIntVar(uint id, PCSolver* solver, VarID varid)
		: IntVar(id, solver, varid) {
}

void IntVar::notifyBacktrack(int, const Lit&) {
	updateBounds();
}

void IntVar::accept(ConstraintVisitor& ) {
	// FIXME
	//		which id to use (what with internal vars)
	//		also add eq and diseq reifs? (can occur in other constraints!)
}

rClause IntVar::notifypropagate() {
	Weight lastmin = currentmin, lastmax = currentmax;
	updateBounds();
	if (lastmin != currentmin || lastmax != currentmax) {
		if (verbosity() > 7) {
			clog << ">>> After bounds update: var range is " << toString(getVarID()) << "[" << currentmin << "," << currentmax << "]\n";
		}
		engine().notifyBoundsChanged(this);
	}

	return nullPtrClause;
}

Lit IntVar::getEQLit(Weight bound) {
	auto it = eqlits.find(bound);
	if(it!=eqlits.cend()){
		return it->second;
	}
	auto head = getPCSolver().getLit(getVarID(), EqType::EQ, bound);

// Adding equality theory turns out to be expensive
/*	for(auto bound2eq : eqlits){
		auto othereq = bound2eq.second;
		add(Implication(getID(), head, ImplicationType::IMPLIES, { ~othereq }, true));
		add(Implication(getID(), othereq, ImplicationType::IMPLIES, { ~head }, true));
	}*/

//	auto firstact = engine().getActivity(getGEQLit(bound).getAtom());
//	auto secondact = engine().getActivity(getLEQLit(bound).getAtom());
//	auto act = (firstact + secondact) / 2 + 0.00001; // A slight higher activity of equal literals
//	engine().setActivity(head.getAtom(), act); // TODO in krinkelplanning, good for lazy, not for non-lazy

	eqlits[bound] = head;
	add(Implication(getID(), head, ImplicationType::EQUIVALENT, { getGEQLit(bound), getLEQLit(bound) }, true));
	return head;
}

void IntVar::addConstraint(IntVarValue const * const prev, const IntVarValue& lv, IntVarValue const * const next) {
	// leq[i] => leq[i+1]
	if (next != NULL) {
		add(Disjunction(getID(), { ~getLEQLit(lv.value), getLEQLit(next->value) }));
	} else if (lv.value == origMaxValue()) {
		add(Disjunction(getID(), { getLEQLit(lv.value) }));
	}

	//~leq[i] => ~leq[i-1]
	if (prev != NULL) {
		add(Disjunction(getID(), { getLEQLit(lv.value), ~getLEQLit(prev->value) }));
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
		if (i < leqlits.size() - 1) {
			next = &leqlits[i + 1];
		}
		IntVarValue* prev = NULL;
		if (i > 0) {
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
		if (not isFalse(i->lit)) { // First non-false is lowest remaining value
			currentmin = i->value;
			break;
		}
	}

	bool found = false;
	for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) { // NOTE: reverse iterated!
		if (not isTrue(i->lit)) { // First non true => previous is highest remaining value (LEQ!)
			if(i==leqlits.crbegin()){
				return; // Conflict, will be resolved by unit propagation anyway
			}
			currentmax = (--i)->value;
			found = true;
			break;
		}
	}
	if (not found) {
		currentmax = leqlits.front().value;
	}
	// clog <<"Updated bounds for var" <<toString(getVarID()) <<" to ["<<minValue() <<"," <<maxValue() <<"]\n";
}

RangeIntVar::RangeIntVar(uint id, PCSolver* solver, VarID varid, Weight min, Weight max)
		: BasicIntVar(id, solver, varid) {
	if (min > max) {
		getPCSolver().notifyUnsat(); //FIXME not able to explain this atm
		notifyNotPresent(); // FIXME what if the explanation is required later on? => check reason list before deleting
		return;
	}
	if(isNegInfinity(min) || isPosInfinity(max)){
		throw idpexception("Values of rangevar cannot be infinite");
	}
	setOrigMax(max);
	setOrigMin(min);
}

void RangeIntVar::finish() {
	for (Weight i = origMinValue(); i <= origMaxValue(); ++i) {
		auto var = engine().getLit(getVarID(), EqType::LEQ, i);
		leqlits.push_back(IntVarValue(this, var, i));
		engine().accept(this, var, FASTEST);
		engine().accept(this, ~var, FASTEST);
		if(origMaxValue()==getMaxElem<Weight>()){ // TODO very ugly overflow check, necessary for min and max aggregates (empty set is infinity)
			break;
		}
	}

	for (Weight i = origMinValue(); i < origMaxValue() + 1; ++i) {
		getPCSolver().varBumpActivity(var(getEQLit(i)));
		getPCSolver().varBumpActivity(var(getEQLit(i)));
		getPCSolver().varBumpActivity(var(getEQLit(i)));
		getPCSolver().varBumpActivity(var(getEQLit(i)));
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().acceptBounds(new IntView(this, 0), this);

	addConstraints();
	engine().notifyBoundsChanged(this);
}

Lit RangeIntVar::getLEQLit(Weight bound) {
	if(verbosity()>5){
		clog <<"Requesting var" <<toString(getVarID()) <<"[" <<minValue() <<"," <<maxValue() <<"]" <<"=<" <<bound <<" (orig bounds" <<"[" <<origMinValue() <<"," <<origMaxValue() <<"]"  <<")\n";
	}
	if(origMinValue()>0 && negInfinity()+origMinValue()>bound){
		return getPCSolver().getFalseLit();
	}
	if(origMinValue()<0 && posInfinity()+origMinValue()<bound){
		return getPCSolver().getTrueLit();
	}
	auto ti = bound - origMinValue();
	MAssert(ti>=Weight(0) && ti<=Weight(getMaxElem<int>()));
	if (ti < Weight(0)) {
		return getPCSolver().getFalseLit();
	}
	if (Weight((int)leqlits.size()) <= ti) {
		return getPCSolver().getTrueLit();
	}
	return leqlits[(int)ti].lit;
}

Lit RangeIntVar::getGEQLit(Weight bound) {
	if(bound==negInfinity()){
		return getPCSolver().getTrueLit();
	}
	return not getLEQLit(bound - 1);
}

EnumIntVar::EnumIntVar(uint id, PCSolver* solver, VarID varid, const std::vector<Weight>& values)
		: BasicIntVar(id, solver, varid), _values(values) {
	for(auto w: values){
		if(isPosInfinity(w) || isNegInfinity(w)){
			throw idpexception("Values of enumvar cannot be infinite");
		}
	}
	if (values.empty()) {
		getPCSolver().notifyUnsat(); //FIXME not able to explain this atm
		notifyNotPresent();
		return;
	}
	sort(_values.begin(), _values.end());
	setOrigMin(_values.front());
	setOrigMax(_values.back());
}

void EnumIntVar::finish(){
	for (auto i = _values.cbegin(); i < _values.cend(); ++i) {
		auto var = engine().getLit(getVarID(), EqType::LEQ, *i);
		leqlits.push_back(IntVarValue(this, var, *i));
		engine().accept(this, var, FASTEST);
		engine().accept(this, ~var, FASTEST);
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().acceptBounds(new IntView(this, 0), this);

	addConstraints();
	engine().notifyBoundsChanged(this);
}

Lit EnumIntVar::getLEQLit(Weight bound) {
	if(verbosity()>5){
		clog <<"Requesting var" <<toString(getVarID()) <<"{" <<minValue() <<",...," <<maxValue() <<"}" <<"=<" <<bound <<" (orig bounds" <<"{" <<origMinValue() <<",...)," <<origMaxValue() <<"}"  <<")\n";
	}
	if (origMaxValue() < bound) {
		return getPCSolver().getTrueLit();
	} else if (bound < origMinValue()) {
		return getPCSolver().getFalseLit();
	} else {
		for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) {
			if (i->value <= bound) {
				return i->lit;
			}
		}
		throw idpexception("Invalid code path");
	}
}

Lit EnumIntVar::getGEQLit(Weight bound) {
	if(verbosity()>5){
		clog <<"Requesting var" <<toString(getVarID()) <<"{" <<minValue() <<",...," <<maxValue() <<"}" <<">=" <<bound <<" (orig bounds" <<"{" <<origMinValue() <<",...," <<origMaxValue() <<"}"  <<")\n";
	}
	if (bound <= origMinValue()) {
		return getPCSolver().getTrueLit();
	} else if (origMaxValue() < bound) {
		return getPCSolver().getFalseLit();
	} else {
		for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) {
			if (i->value < bound) {
				return ~i->lit;
			} else if (bound == i->value) {
				return ~((++i)->lit);
			}
		}
		throw idpexception("Invalid code path");
	}
}
