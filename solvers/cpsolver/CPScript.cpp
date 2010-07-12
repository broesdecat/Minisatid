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
		boolvars.insert(boolvars.begin(), s.getBoolVars().begin(), s.getBoolVars().end());
		intvars.insert(intvars.begin(), s.getIntVars().begin(), s.getIntVars().end());

		for(int i=0; i<boolvars.size(); i++){
			boolvars[i].update(*this, share, s.boolvars[i]);
		}

		for(int i=0; i<intvars.size(); i++){
			intvars[i].update(*this, share, s.intvars[i]);
		}
	}

	CPScript* CPScript::copy(bool share){
		return new CPScript(share, *this);
	}
}
