/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/cpsolver/CPScript.hpp"
#include "modules/cpsolver/CPUtils.hpp"
#include "external/ConstraintVisitor.hpp"

using namespace std;

using namespace MinisatID;
using namespace Gecode;

CPScript::CPScript(): Space(){

}

CPScript::CPScript(bool share, CPScript& s): Space(share, s){
	for(auto i=s.boolvars.begin(); i<s.boolvars.end(); i++){
		boolvars.push_back(Gecode::BoolVar());
		boolvars.back().update(*this, share, *i);
	}

	for(auto i=s.intvars.begin(); i<s.intvars.end(); i++){
		intvars.push_back(Gecode::IntVar());
		intvars.back().update(*this, share, *i);
	}
}

CPScript* CPScript::copy(bool share){
	return new CPScript(share, *this);
}

intvarindex CPScript::addIntVar(int min, int max){
	intvars.push_back(Gecode::IntVar(*this, min, max));
	return intvars.size()-1;
}

intvarindex CPScript::addIntVar(const vector<int>& values){
	auto set = IntSet(values.data(), values.size());
	intvars.push_back(Gecode::IntVar(*this, set));
	return intvars.size()-1;
}

boolvarindex CPScript::addBoolVar(){
	boolvars.push_back(Gecode::BoolVar(*this, 0, 1));
	return boolvars.size()-1;
}

void CPScript::accept(ConstraintVisitor& visitor){
	int id = 1;
	for(auto i=intvars.cbegin(); i<intvars.cend(); ++i){
		visitor.add(IntVarRange({id++}, i->min(), i->max()));
	}
}

void CPScript::addBranchers(){
	IntVarArgs x(intvars.size());
	for(vintv::size_type i=0; i<intvars.size(); i++){
		x[i]=intvars[i];
	}
	branch(*this, x, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MAX);
}

ostream& MinisatID::operator <<(ostream& stream, const CPScript& script){
	stream <<"Space:\n";
	int count = 0;
	for(vintv::const_iterator i=script.getIntVars().cbegin(); i<script.getIntVars().cend(); i++){
		Int::IntView v(*i);
		stream << "var " <<count++ << "=" <<v <<"; ";
		if(count%10 == 0){
			stream <<"\n";
		}
	}
	stream <<"\n";
	return stream;
}
