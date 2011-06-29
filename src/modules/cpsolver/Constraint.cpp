/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/cpsolver/Constraint.hpp"

#include "modules/cpsolver/CPScript.hpp"
#include "modules/cpsolver/CPUtils.hpp"

#include "utils/Print.hpp"

using namespace std;

using namespace MinisatID;
using namespace Gecode;

TermIntVar::TermIntVar():range(false), min(-1), max(-1), var(-1){	}

TermIntVar::TermIntVar(CPScript& space, int groundterm, int min, int max):
		ID(groundterm), range(false), min(min), max(max), var(space.addIntVar(min, max)){
}

TermIntVar::TermIntVar(CPScript& space, int groundterm, const vector<int>& values):
		ID(groundterm), range(false), min(-1), max(-1), values(values), var(space.addIntVar(values)){
}

Gecode::IntVar 	TermIntVar::getIntVar(const CPScript& space) const {
	return space.getIntVars()[var];
}

ReifiedConstraint::ReifiedConstraint(Var atom, CPScript& space): head(atom), var(space.addBoolVar()){
}

Gecode::BoolVar ReifiedConstraint::getBoolVar(const CPScript& space) const {
	return space.getBoolVars()[var];
}

rClause ReifiedConstraint::propagate(bool becametrue, CPScript& space){
	assert(!isAssigned(space));

	rel(space, getBoolVar(space), IRT_EQ, becametrue?1:0);

	return nullPtrClause;
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, TermIntVar rhs, Var atom)
		: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(false), trhs(rhs), withmult(false){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	linear(space, ar, rel, trhs.getIntVar(space), getBoolVar(space)/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int rhs, Var atom)
		: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs), withmult(false){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	linear(space, ar, rel, irhs, getBoolVar(space)/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, TermIntVar rhs, Var atom)
		: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(false), trhs(rhs), withmult(true), mult(mult){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	IntArgs ia(mult.size());
	for(vector<int>::size_type i=0; i<mult.size(); i++){
		ia[i]=mult[i];
	}
	linear(space, ia, ar, rel, trhs.getIntVar(space), getBoolVar(space)/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, int rhs, Var atom)
		: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs), withmult(true), mult(mult){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	IntArgs ia(mult.size());
	for(vector<int>::size_type i=0; i<mult.size(); i++){
		ia[i]=mult[i];
	}
	linear(space, ia, ar, rel, irhs, getBoolVar(space)/*,consistency level*/);
}

CountConstraint::CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int value, TermIntVar rhs)
		: set(tset.size()), rel(rel), intrhs(false), trhs(rhs){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}

	count(space, ar, value, rel, trhs.getIntVar(space)/*,consistency level*/);
}



BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, TermIntVar rhs, Var atom)
		: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(false), trhs(rhs){
	IntVar ialhs = lhs.getIntVar(space), iarhs = trhs.getIntVar(space);

	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space), ICL_DOM);
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, Var atom)
		: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(true), irhs(rhs){
	//clog <<"Adding constraint " <<getPrintableVar(atom) <<" <=> " <<lhs <<rel <<rhs <<".\n";
	IntVar ialhs = lhs.getIntVar(space);
	int iarhs = irhs;
	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space), ICL_DOM);
}

DistinctConstraint::DistinctConstraint(CPScript& space, vector<TermIntVar> tset)
		: set(tset.size()){
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i].getIntVar(space);
	}
	distinct(space, set, ICL_DOM);
}

//Atmostone NON REIF
//min max abs mult NON REIF

ostream& MinisatID::operator<< (ostream& os, const TermIntVar& tiv){
	return os <<tiv.ID <<"[" <<tiv.min <<"," <<tiv.max <<"]";
}
