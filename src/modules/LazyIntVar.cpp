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

// NOTE: currently always grounds at least log(max-min) elements.
// TODO Could be changed to be able to only ground at least 2 elements.

LazyIntVar::LazyIntVar(PCSolver* solver, int _origid, int min, int max)
		: IntVar(solver, _origid){
	setOrigMax(max);
	setOrigMin(min);

	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_STATEFUL);
	getPCSolver().acceptBounds(new IntView(this, 0), this);

	checkAndAddVariable((min+max)/2);

	engine().notifyBoundsChanged(this);
}

//Add a variable for var =< value
Lit LazyIntVar::addVariable(int value){
//	cerr <<"Adding variable with value " <<value <<" for var " <<origid() <<"\n";
	if(value>origMaxValue()){
		return getPCSolver().getTrueLit();
	}
	if(value<origMinValue()){
		return getPCSolver().getFalseLit();
	}
	uint i=0;
	for(; i<leqlits.size(); ++i) {
		const auto& lq = leqlits[i];
		MAssert(lq.value!=value);
		if(lq.value>value){
			break;
		}
	}

	auto var = engine().newVar();
	leqlits.insert(leqlits.begin()+i, IntVarValue(this, var, value));
#ifdef DEBUG
	bool found = false;
//	cerr <<"Var" <<origid() <<" is grounded for ";
	for(auto j=leqlits.cbegin(); j<leqlits.cend(); ++j) {
//		cerr <<j->value <<" ";
		if((j+1)<leqlits.cend()){
			MAssert(j->value < (j+1)->value);
		}
		if(j->value==value){
			found = true;
		}
	}
//	cerr <<"\n";
	MAssert(found);
#endif
	engine().accept(this, mkPosLit(var), FASTEST);
	engine().accept(this, mkNegLit(var), FASTEST);
	if (verbosity() > 3) {
		clog << toString(mkPosLit(var)) << " <=> " << "var" << origid() << "=<" << value << "\n";
	}
	if(value==origMaxValue()){
		internalAdd(Disjunction( { mkPosLit(var) }), engine());
	}
	IntVarValue* next = NULL;
	if((i+1)<leqlits.size()){
		next = &(leqlits[i+1]);
	}
	IntVarValue* prev = NULL;
	if(i>0){
		prev = &(leqlits[i-1]);
	}
	addConstraint(prev, leqlits[i], next);
	return mkPosLit(var);
}

void LazyIntVar::saveState(){
	savedleqlits = leqlits;
}
void LazyIntVar::resetState(){
	leqlits = savedleqlits; // TODO remove watches on older literals from the queue
	updateBounds();
}

/**
 * lazy intvar:
 *
 * introduce one variable
 * When it is assigned a value, introduce one within the relevant remaining interval
 * If there are two vars which are consecutive in the full interval and one is false and the other one true, then no more introduction is necessary
 */

void LazyIntVar::updateBounds() {
/*	cerr <<"For var" <<origid() <<":\n";
	for (auto i = leqlits.cbegin(); i < leqlits.cend(); ++i) {
		cerr <<toString(mkPosLit(i->atom)) << "<=> var" <<origid() <<"=<" <<i->value <<"\n";
	}
	cerr <<"\n";*/
	int prev = origMinValue();
	for (auto i = leqlits.cbegin(); i < leqlits.cend(); ++i) {
		if (not isFalse(mkPosLit(i->atom))) { // First non-false: then previous one +1 is lowest remaining value
			break;
		}
		prev = i->value+1;
	}
	currentmin = prev;

	int next = origMaxValue();
	for (auto i = leqlits.crbegin(); i < leqlits.crend(); ++i) { // NOTE: reverse iterated!
		if (not isTrue(mkPosLit(i->atom))) { // First non true:  => previous is highest remaining value (LEQ!)
			break;
		}
		next = i->value;
	}
	currentmax = next;

	//MAssert(isTrue(getGEQLit(minValue())));
	//MAssert(isTrue(getLEQLit(maxValue())));

	// Note: Forces existence of the var TODO in fact enough if there is already SOME var in that interval!
	if(not checkAndAddVariable(currentmin)){
		if(not checkAndAddVariable(currentmax)){
			checkAndAddVariable((currentmin+currentmax)/2);
		}
	}
//	cerr <<"Updated bounds for var" <<origid() <<" to ["<<minValue() <<"," <<maxValue() <<"]\n";
}

struct CompareVarValue{
	bool operator() (const IntVarValue& left, const IntVarValue& right) const{
		return left.value < right.value;
	}
};

template<class List>
typename List::const_iterator findVariable(int value, const List& list){
	auto i = lower_bound(list.cbegin(), list.cend(), IntVarValue(NULL, -1,value), CompareVarValue());
	if(i!=list.cend() && i->value==value){
		return i;
	}else{
		return list.cend();
	}
}

bool LazyIntVar::checkAndAddVariable(int value){ // Returns true if it was newly created
//	cerr <<"Checking for value " <<value <<" for var " <<origid() <<"\n";
	auto i = findVariable(value, leqlits);
#ifdef DEBUG
	for(auto j=leqlits.cbegin(); j<leqlits.cend(); ++j) {
		if(j->value==value){
			MAssert(i==j);
			MAssert(i!=leqlits.end() && i->value==value);
		}
	}
#endif
	if(i!=leqlits.end()){
		return false;
	}else{
		addVariable(value);
		return true;
	}
}

Lit LazyIntVar::getLEQLit(int bound) {
//	cerr <<"Requesting var" <<origid() <<"{" <<origMinValue() <<",()," <<origMaxValue() <<"}" <<">=" <<bound <<"\n";
	if (origMaxValue() < bound) {
		return getPCSolver().getTrueLit();
	} else if (bound < origMinValue()) {
		return getPCSolver().getFalseLit();
	} else {
		auto i = findVariable(bound, leqlits);
		if(i!=leqlits.cend()){
			return mkPosLit(i->atom);
		}else{
			return addVariable(bound);
		}
	}
}

Lit LazyIntVar::getGEQLit(int bound) {
	return not getLEQLit(bound-1);
}