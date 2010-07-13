/*
 * CPScript.cpp
 *
 *  Created on: Jul 12, 2010
 *      Author: broes
 */

#include "solvers/cpsolver/CPScript.hpp"

namespace CP{
	CPScript::CPScript(): Space(){

	}

	CPScript::CPScript(bool share, CPScript& s): Space(share, s){
		for(int i=0; i<s.boolvars.size(); i++){
			boolvars.push_back(BoolVar());
			boolvars[i].update(*this, share, s.boolvars[i]);
		}

		for(int i=0; i<s.intvars.size(); i++){
			intvars.push_back(IntVar());
			intvars[i].update(*this, share, s.intvars[i]);
		}
	}

	CPScript* CPScript::copy(bool share){
		cout <<"Copying space" <<endl;
		return new CPScript(share, *this);
	}

	ostream& operator <<(ostream& ostream, const CPScript& script){
		ostream <<"Space:" <<endl;
		for(int i=0; i<script.getBoolVars().size(); i++){
			ostream << script.getBoolVars()[i] <<endl;
		}

		for(int i=0; i<script.getIntVars().size(); i++){
			Int::IntView v(script.getIntVars()[i]);
			std::cout << "var " <<i << "=" <<v <<"; ";
			//ostream << script.getIntVars()[i] <<endl;
		}
		return ostream;
	}
}
