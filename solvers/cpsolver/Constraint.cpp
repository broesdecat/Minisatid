/*
 * Constraint.cpp
 *
 *  Created on: Jul 27, 2010
 *      Author: broes
 */

#include "solvers/cpsolver/Constraint.hpp"

using namespace CP;

ReifiedConstraint::ReifiedConstraint(int atom, CPScript& space): atom(atom), var(space.addBoolVar()){
}

void ReifiedConstraint::propagate(bool becametrue, CPScript& space){
	//TODO should be checked, but maybe this complicates which solver queues and which have to be propagated
	//assert(!isAssigned(space));
	//if(isAssigned(space)){
	//	return;
	//}

	rel(space, getBoolVar(space), IRT_EQ, becametrue?1:0);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, TermIntVar rhs, int atom)
	: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(false),
	  trhs(rhs), withmult(false){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	linear(space, ar, rel, trhs.getIntVar(space), getBoolVar(space)/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int rhs, int atom)
	: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs), withmult(false){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	linear(space, ar, rel, irhs, getBoolVar(space)/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, TermIntVar rhs, int atom)
	: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(false),
	  trhs(rhs), withmult(true), mult(mult){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	IntArgs ia(mult.size());
	for(int i=0; i<mult.size(); i++){
		ia[i]=mult[i];
	}
	linear(space, ia, ar, rel, trhs.getIntVar(space), getBoolVar(space)/*,consistency level*/);
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, vector<int> mult, IntRelType rel, int rhs, int atom)
	: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(true), irhs(rhs), withmult(true), mult(mult){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}
	IntArgs ia(mult.size());
	for(int i=0; i<mult.size(); i++){
		ia[i]=mult[i];
	}
	linear(space, ia, ar, rel, irhs, getBoolVar(space)/*,consistency level*/);
}

ostream& CP::operator<< (ostream& os, const TermIntVar& tiv){
	return os <<tiv.ID <<"[" <<tiv.min <<"," <<tiv.max <<"]";
}

CountConstraint::CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int value, TermIntVar rhs)
	: set(tset.size()), rel(rel), intrhs(false), trhs(rhs){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}

	/*cout <<"Added Count(";
	for(vector<TermIntVar>::const_iterator i=tset.begin(); i<tset.end(); i++){
		cout << (*i) <<"=" <<value <<", ";
	}
	cout <<") " <<rel <<" " << rhs <<endl;*/

	count(space, ar, value, rel, trhs.getIntVar(space)/*,consistency level*/);
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
	: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(false), trhs(rhs){
	IntVar ialhs = lhs.getIntVar(space), iarhs = trhs.getIntVar(space);

	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space));
}

BinArithConstraint::BinArithConstraint(CPScript& space, TermIntVar lhs, IntRelType rel, int rhs, int atom)
	: ReifiedConstraint(atom, space), lhs(lhs), rel(rel), intrhs(true), irhs(rhs){
	IntVar ialhs = lhs.getIntVar(space);
	int iarhs = irhs;
	Gecode::rel(space, ialhs, rel, iarhs, getBoolVar(space) );
}

DistinctConstraint::DistinctConstraint(CPScript& space, vector<TermIntVar> tset)
	: set(tset.size()){
	for(int i=0; i<tset.size(); i++){
		set[i] = tset[i].getIntVar(space);
	}
	distinct(space, set);
}

//Atmostone NON REIF
//min max abs mult (arithmetic constraints) NON REIF
