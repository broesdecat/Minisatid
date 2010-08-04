//--------------------------------------------------------------------------------------------------
//    Copyright (c) 2009-2010, Broes De Cat, K.U.Leuven, Belgium
//    
//    Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
//    associated documentation files (the "Software"), to deal in the Software without restriction,
//    including without limitation the rights to use, copy, modify, merge, publish, distribute,
//    sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
//    furnished to do so, subject to the following conditions:
//    
//    The above copyright notice and this permission notice shall be included in all copies or
//    substantial portions of the Software.
//    
//    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
//    NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
//    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
//    OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//--------------------------------------------------------------------------------------------------

#include "solvers/cpsolver/Constraint.hpp"

using namespace CP;

ReifiedConstraint::ReifiedConstraint(int atom, CPScript& space): atom(atom), var(space.addBoolVar()){
}

rClause ReifiedConstraint::propagate(bool becametrue, CPScript& space){
	assert(!isAssigned(space));

	rel(space, getBoolVar(space), IRT_EQ, becametrue?1:0);

	return nullPtrClause;
}

SumConstraint::SumConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, TermIntVar rhs, int atom)
		: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(false), trhs(rhs), withmult(false){
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
		: ReifiedConstraint(atom, space), set(tset.size()), rel(rel), intrhs(false), trhs(rhs), withmult(true), mult(mult){
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

CountConstraint::CountConstraint(CPScript& space, vector<TermIntVar> tset, IntRelType rel, int value, TermIntVar rhs)
		: set(tset.size()), rel(rel), intrhs(false), trhs(rhs){
	IntVarArgs ar(tset.size());
	for(vector<TermIntVar>::size_type i=0; i<tset.size(); i++){
		set[i] = tset[i];
		ar[i] = tset[i].getIntVar(space);
	}

	count(space, ar, value, rel, trhs.getIntVar(space)/*,consistency level*/);
}



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
//min max abs mult NON REIF

ostream& CP::operator<< (ostream& os, const TermIntVar& tiv){
	return os <<tiv.ID <<"[" <<tiv.min <<"," <<tiv.max <<"]";
}
