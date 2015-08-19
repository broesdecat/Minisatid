/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/IntVar.hpp"
#include <iostream>
#include "utils/Print.hpp"
#include "external/ConstraintVisitor.hpp"
#include "satsolver/SATSolver.hpp"

using namespace MinisatID;
using namespace std;

// NOTE: currently always grounds at least log(max-min) elements.
// TODO Could be changed to be able to only ground at least 2 elements.

LazyIntVar::LazyIntVar(PCSolver* solver, VarID varid, Weight min, Weight max, Lit partial)
		: IntVar(solver, varid, partial), halve(true){
	setOrigMax(max);
	setOrigMin(min);
	//clog <<"Created lazy variable " <<toString(varid) <<" = [" <<min <<", " <<max <<"]\n";
}

void LazyIntVar::finish(){
	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().acceptBounds(getPCSolver().getIntView(this->getVarID(), 0), this);

	Weight val(0);
#ifdef NOARBITPREC
	val = (origMinValue()+origMaxValue())/2;
#else
	if(isNegInfinity(origMinValue()) || isPosInfinity(origMaxValue())){
		val = 0;
	}else{
		val = (origMinValue()+origMaxValue())/2;
	}
#endif

	checkAndAddVariable(val);
	engine().notifyBoundsChanged(this);
}

//Add a variable for var =< value
Lit LazyIntVar::addVariable(Weight value){
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

	auto var = engine().getLit(getVarID(), EqType::LEQ, value);

	auto firstat = i>0?(leqlits.begin()+i-1)->lit.getAtom():Minisat::var_Undef;
	auto secondat = i+1<leqlits.size()?(leqlits.begin()+i+1)->lit.getAtom():Minisat::var_Undef;
	engine().notifyHeuristicOfLazyAtom(var.getAtom(), firstat, secondat); // TODO: ask broes what this actually means...

	leqlits.insert(leqlits.begin()+i, IntVarValue(this, var, value));

#ifdef DEBUG
	bool found = false;
	for(auto j=leqlits.cbegin(); j<leqlits.cend(); ++j) {
		if((j+1)<leqlits.cend()){
			MAssert(j->value < (j+1)->value);
		}
		if(j->value==value){
			found = true;
		}
	}
	MAssert(found);
#endif

	engine().accept(this, var, FASTEST);
	engine().accept(this, ~var, FASTEST);
	if(value==origMaxValue()){
		add(Disjunction({ var }));
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
	return var;
}

/**
 * lazy intvar:
 *
 * introduce one variable
 * When it is assigned a value, introduce one within the relevant remaining interval
 * If there are two vars which are consecutive in the full interval and one is false and the other one true, then no more introduction is necessary
 */

void LazyIntVar::updateBounds() {
	auto newmin = origMinValue();
	auto newmax = origMaxValue();

	auto unknown = false;
	if(not possiblyHasImage()) {
		return;
	}

	// leqlit: var <= value
	// Prerequisite: leqlits are ordered from low value to high
	for (auto leqlit:leqlits){
		if(isFalse(leqlit.lit)){ //(Last value for which var <= value holds)+1 is the lower bound of var.
#ifdef NOARBITPREC
			MAssert(leqlit.value != getMaxElem<Weight>());
#endif
			newmin = max(leqlit.value+1, newmin);
			unknown = false;
		}
		if(isUnknown(leqlit.lit)){ // If any leqlit is unknown after the last false, then set unknown  to true.
			unknown = true;
		}
		if(isTrue(leqlit.lit)){//First value for which var <= value holds is the upper bound of var.
			newmax = min(leqlit.value, newmax); //In a strict sense, we don't need the min operation here.
			break;
		}
	}

	currentmin = newmin;
	currentmax = newmax;

	// TODO infinite case
	// Note: Forces existence of the var TODO in fact enough if there is already SOME var in that interval!
	if(not unknown && not checkAndAddVariable(currentmin) && not checkAndAddVariable(currentmax)){
		if(halve){
			checkAndAddVariable((currentmin+currentmax)/2);
		}else{
			checkAndAddVariable(currentmax-1);
			checkAndAddVariable(currentmin+1);
		}
		halve = not halve;
	}
	if(verbosity()>5){
		clog <<"Updated bounds for var" <<toString(getVarID()) <<" to ["<<minValue() <<"," <<maxValue() <<"]\n";
	}
}

struct CompareVarValue{
	bool operator() (const IntVarValue& left, const IntVarValue& right) const{
		return left.value < right.value;
	}
};

template<class List>
typename List::const_iterator findVariable(Weight value, const List& list){
	auto i = lower_bound(list.cbegin(), list.cend(), IntVarValue(NULL, mkPosLit(1),value), CompareVarValue());
	if(i!=list.cend() && i->value==value){
		return i;
	}else{
		return list.cend();
	}
}

bool LazyIntVar::checkAndAddVariable(Weight value){ // Returns true if it was newly created
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
		getPCSolver().notifyGroundingCall();
		addVariable(value);
		return true;
	}
}

Lit LazyIntVar::getLEQLit(Weight bound) {
	if(verbosity()>5){
		clog <<"Requesting var" <<getVarID().id <<"{" <<origMinValue() <<",()," <<origMaxValue() <<"}" <<"=<" <<bound <<"\n";
	}
	if (origMaxValue() <= bound) {
		return getPCSolver().getTrueLit();
	} else if (bound < origMinValue()) {
		return getPCSolver().getFalseLit();
	} else {
		auto i = findVariable(bound, leqlits);
		if(i!=leqlits.cend()){
			return i->lit;
		}else{
			return addVariable(bound);
		}
	}
}

Lit LazyIntVar::getGEQLit(Weight bound) {
	if(bound==getMinElem<int>()){
		return getPCSolver().getTrueLit();
	}
	return not getLEQLit(bound-1);
}
