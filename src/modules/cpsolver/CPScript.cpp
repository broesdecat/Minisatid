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

using namespace std;

using namespace MinisatID;
using namespace CP;

using namespace Gecode;

CPScript::CPScript(): Space(){

}

CPScript::CPScript(bool share, CPScript& s): Space(share, s){
	for(vboolv::iterator i=s.boolvars.begin(); i<s.boolvars.end(); i++){
		boolvars.push_back(BoolVar());
		boolvars.back().update(*this, share, *i);
	}

	for(vintv::iterator i=s.intvars.begin(); i<s.intvars.end(); i++){
		intvars.push_back(IntVar());
		intvars.back().update(*this, share, *i);
	}
}

CPScript* CPScript::copy(bool share){
	return new CPScript(share, *this);
}

intvarindex CPScript::addIntVar(int min, int max){
	intvars.push_back(IntVar(*this, min, max));
	return intvars.size()-1;
}

boolvarindex CPScript::addBoolVar(){
	boolvars.push_back(BoolVar(*this, 0, 1));
	return boolvars.size()-1;
}

void CPScript::addBranchers(){
	IntVarArgs x(intvars.size());
	for(vintv::size_type i=0; i<intvars.size(); i++){
		x[i]=intvars[i];
	}
	branch(*this, x, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MAX);
}

ostream& CP::operator <<(ostream& ostream, const CPScript& script){
	ostream <<"Space:" <<endl;
	/*for(vboolv::const_iterator i=script.getBoolVars().begin(); i<script.getBoolVars().end(); i++){
		ostream << *i <<" " <<endl;
	}*/

	int count = 0;
	for(vintv::const_iterator i=script.getIntVars().begin(); i<script.getIntVars().end(); i++){
		Int::IntView v(*i);
		std::cout << "var " <<count++ << "=" <<v <<"; ";
		if(count%10 == 0){
			ostream <<endl;
		}
	}
	ostream <<endl;
	return ostream;
}
