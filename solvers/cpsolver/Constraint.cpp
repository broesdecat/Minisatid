/*
 * Constraint.cpp
 *
 *  Created on: Jul 27, 2010
 *      Author: broes
 */

#include "solvers/cpsolver/Constraint.hpp"

using namespace CP;

Constraint::Constraint(int atom, CPScript& space): atom(atom), var(space.addBoolVar()){
}

void Constraint::propagate(bool becametrue, CPScript& space){
	//TODO should be checked, but maybe this complicates which solver queues and which have to be propagated
	//assert(!isAssigned(space));
	/*if(isAssigned(space)){
		return;
	}*/
	//cout <<"Before rel" << space.getBoolVars()[getBoolVar()] <<endl;
	//BoolVar v(space, 0, 1);
	//rel(space, v, IRT_GQ, becametrue?1:0);
	rel(space, space.getBoolVars()[getBoolVar()], IRT_EQ, becametrue?1:0);
	//Int::BoolView v(space.getBoolVars()[getBoolVar()]);
	//v.eq(space, becametrue?1:0);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, TermIntVar rhs, int atom)
	: Constraint(atom, space), set(tset.size()), rel(rel), intrhs(false),
	  trhs(rhs), withmult(false){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = space.getIntVars()[tset[i].var];
	}
	linear(space, ar, rel, space.getIntVars()[trhs.var], space.getBoolVars()[getBoolVar()]/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int rhs, int atom)
	: Constraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs), withmult(false){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = space.getIntVars()[tset[i].var];
	}
	linear(space, ar, rel, irhs, space.getBoolVars()[getBoolVar()]/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, TermIntVar rhs, int atom)
	: Constraint(atom, space), set(tset.size()), rel(rel), intrhs(false),
	  trhs(rhs), withmult(true), mult(mult){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = space.getIntVars()[tset[i].var];
	}
	IntArgs ia(mult.size());
	for(int i=0; i<mult.size(); i++){
		ia[i]=mult[i];
	}
	linear(space, ia, ar, rel, space.getIntVars()[trhs.var], space.getBoolVars()[getBoolVar()]/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, int rhs, int atom)
	: Constraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs), withmult(true), mult(mult){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = space.getIntVars()[tset[i].var];
	}
	IntArgs ia(mult.size());
	for(int i=0; i<mult.size(); i++){
		ia[i]=mult[i];
	}
	linear(space, ia, ar, rel, irhs, space.getBoolVars()[getBoolVar()]/*,consistency level*/);
}

ostream& CP::operator<< (ostream& os, const TermIntVar& tiv){
	return os <<tiv.term <<"[" <<tiv.min <<"," <<tiv.max <<"]";
}

CountConstraint::CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int value, TermIntVar rhs)
	: set(tset.size()), rel(rel), intrhs(false), trhs(rhs){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = space.getIntVars()[tset[i].var];
	}

	/*cout <<"Added Count(";
	for(vector<TermIntVar>::const_iterator i=tset.begin(); i<tset.end(); i++){
		cout << (*i) <<"=" <<value <<", ";
	}
	cout <<") " <<rel <<" " << rhs <<endl;*/

	count(space, ar, value, rel, space.getIntVars()[trhs.var]/*,consistency level*/);
}

//	CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int rhs)
//		: set(tset.size()), rel(rel), intrhs(true), irhs(rhs){
//		IntVarArgs ar(tset.size());
//		for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
//			set[i] = tset[i];
//			ar[i] = space.getIntVars()[tset[i].var];
//		}
//		//count(space, ar, rel, irhs/*,consistency level*/);
//	}


BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, TermIntVar rhs, int atom)
	: Constraint(atom, space), lhs(lhs), rel(rel), intrhs(false), trhs(rhs){
	IntVar ialhs = space.getIntVars()[lhs.var], iarhs = space.getIntVars()[trhs.var];

	Gecode::rel(space, ialhs, rel, iarhs, space.getBoolVars()[getBoolVar()]);
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, int atom)
	: Constraint(atom, space), lhs(lhs), rel(rel), intrhs(true), irhs(rhs){
	IntVar ialhs = space.getIntVars()[lhs.var];
	int iarhs = irhs;
	Gecode::rel(space, ialhs, rel, iarhs, space.getBoolVars()[getBoolVar()] );
}

DistinctConstraint::DistinctConstraint(CPScript& space, vector<TermIntVar> tset)
	: set(tset.size()){
	for(int i=0; i<tset.size(); i++){
		set[i] = space.getIntVars()[tset[i].var];
	}
	distinct(space, set);
}

//Atmostone NON REIF
//min max abs mult (arithmetic constraints) NON REIF
