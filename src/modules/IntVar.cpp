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
		: Propagator(solver, "intvar"), id_(maxid_++), origid_(_origid), engine_(*solver) {
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
		if(i<leqlits.size()-1){
			internalAdd(Disjunction( { ~getLEQLit(leqlits[i].value), getLEQLit(leqlits[i+1].value) }), engine());
		}else{
			internalAdd(Disjunction( { getLEQLit(leqlits[i].value)}), engine());
		}

		//~leq[i] => ~leq[i-1]
		if(i>0){
			internalAdd(Disjunction( { getLEQLit(leqlits[i].value), ~getLEQLit(leqlits[i-1].value)}), engine());
		}
		sometrue.literals.push_back(getLEQLit(leqlits[i].value));
	}
	// some leq is true
	internalAdd(sometrue, engine());
	internalAdd(Disjunction( {getLEQLit(origMaxValue())}), engine());
	internalAdd(Disjunction( {getGEQLit(origMinValue())}), engine());
}

void IntVar::updateBounds() {
	for (auto i=leqlits.cbegin(); i<leqlits.cend(); ++i) {
		if (not isFalse(mkPosLit(i->atom))) { // First non-false is lowest remaining value
			currentmin = i->value;
			break;
		}
	}

	bool found = false;
	for (auto i=leqlits.crbegin(); i<leqlits.crend(); ++i) { // NOTE: reverse iterated!
		if (not isTrue(mkPosLit(i->atom))) { // First non true => previous is highest remaining value (LEQ!)
			currentmax = (--i)->value;
			found = true;
			break;
		}
	}
	if(not found){
		currentmax = leqlits.front().value;
	}
	MAssert(isTrue(getGEQLit(minValue())));
	MAssert(isTrue(getLEQLit(maxValue())));
//	cerr <<"Updated bounds for var" <<origid() <<" to ["<<minValue() <<"," <<maxValue() <<"]\n";
}



RangeIntVar::RangeIntVar(PCSolver* solver, int _origid, int min, int max): IntVar(solver, _origid){
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
		if(verbosity()>3){
			clog << toString(mkPosLit(var)) << " <=> " << "var" << origid() << "=<" << i << "\n";
		}
	}

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().acceptBounds(new IntView(this, 0), this);

	addConstraints();

	engine().notifyBoundsChanged(this);
}

Lit RangeIntVar::getLEQLit(int bound) const {
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

Lit RangeIntVar::getGEQLit(int bound) const {
//	cerr <<"Requesting var" <<origid() <<"[" <<origMinValue() <<"," <<origMaxValue() <<"]" <<">=" <<bound <<"\n";
	auto index = bound - origMinValue() - 1;
	if (index < 0) {
		return getPCSolver().getTrueLit();
	}
	if ((int) leqlits.size() <= index) {
		return getPCSolver().getFalseLit();
	}
	return mkNegLit(leqlits[index].atom);
}


EnumIntVar::EnumIntVar(PCSolver* solver, int _origid, const std::vector<int>& values)
		: IntVar(solver, _origid), _values(values) {
	if(values.empty()){
		getPCSolver().notifyUnsat(); //FIXME not able to explain this atm
		notifyNotPresent();
		return;
	}
	sort(_values.begin(), _values.end());
	setOrigMin(values.front());
	setOrigMax(values.back());

	for (auto i=values.cbegin(); i<values.cend(); ++i) {
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

Lit EnumIntVar::getLEQLit(int bound) const {
//	cerr <<"Requesting var" <<origid() <<"{" <<origMinValue() <<",()," <<origMaxValue() <<"}" <<">=" <<bound <<"\n";
	if(origMaxValue()<bound){
		return getPCSolver().getTrueLit();
	}else if(bound < origMinValue()){
		return getPCSolver().getFalseLit();
	}else{
		for(auto i=leqlits.crbegin(); i<leqlits.crend(); ++i) {
			if(i->value<=bound){
				return mkPosLit(i->atom);
			}
		}
		throw idpexception("Invalid code path");
	}
}

Lit EnumIntVar::getGEQLit(int bound) const {
//	cerr <<"Requesting var" <<origid() <<"{" <<origMinValue() <<",()," <<origMaxValue() <<"}" <<">=" <<bound <<"\n";
	if(bound<=origMinValue()){
		return getPCSolver().getTrueLit();
	}else if(origMaxValue()<bound){
		return getPCSolver().getFalseLit();
	}else{
		for(auto i=leqlits.crbegin(); i<leqlits.crend(); ++i) {
			if(i->value < bound){
				return mkNegLit(i->atom);
			}else if(bound == i->value){
				return mkNegLit((++i)->atom);
			}
		}
		throw idpexception("Invalid code path");
	}
}
