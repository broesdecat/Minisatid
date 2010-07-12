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

	CPScript::CPScript(bool share, CPScript& s): Space(share, s), boolvars(s.boolvars), intvars(s.intvars){
		/*for(int i=0; i<boolvars.size(); i++){
			boolvars[i].update(*this, share, s.boolvars[i]);
		}

		for(int i=0; i<intvars.size(); i++){
			intvars[i].update(*this, share, s.intvars[i]);
		}*/
	}

	CPScript* CPScript::copy(bool share){
		return new CPScript(share, *this);
	}

	ostream& operator <<(ostream& ostream, const CPScript& script){
		ostream <<"Space:" <<endl;
		for(int i=0; i<script.getBoolVars().size(); i++){
			ostream << script.getBoolVars()[i] <<endl;
		}

		for(int i=0; i<script.getIntVars().size(); i++){
			ostream << script.getIntVars()[i] <<endl;
		}
		return ostream;
	}
}
