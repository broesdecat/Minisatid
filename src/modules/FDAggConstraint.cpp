/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "modules/FDAggConstraint.hpp"
#include <iostream>
#include "utils/Print.hpp"

using namespace MinisatID;

FDAggConstraint::FDAggConstraint(PCSolver* engine, IntVar* left, EqType comp, IntVar* right, Var h): Propagator(engine), head_(mkPosLit(h)){

}

void FDAggConstraint::finishParsing(bool& unsat){
	// TODO anything on intvars cannot be accepted before finishparsing of the intvar!
	getPCSolver().accept(this, head(), FAST);
	getPCSolver().accept(this, not head(), FAST);
	for(auto i=set.cbegin(); i!=set.cend(); ++i){
		getPCSolver().acceptBounds(*i, this);
	}
}

rClause FDAggConstraint::getExplanation(const Lit& lit){

}

rClause	FDAggConstraint::notifypropagate(){

}

void FDAggConstraint::printState() const{
	// TODO
}

