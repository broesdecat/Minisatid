/*
 * CPSolverData.cpp
 *
 *  Created on: Jul 27, 2010
 *      Author: broes
 */

#include "solvers/cpsolver/CPSolverData.hpp"

#include "solvers/external/ExternalUtils.hpp"

#include "solvers/utils/Debug.hpp"

using namespace CP;

CPSolverData::CPSolverData(){
	history.push_back(new CPScript());
}

CPSolverData::~CPSolverData(){
	for(int i=0; i<constraints.size(); i++){
		delete constraints[i];
	}
}

bool CPSolverData::allBooleansKnown() const{
	for(int i=0; i<getConstraints().size(); i++){
		if(!getConstraints()[i]->isAssigned(getSpace())){
			reportf("Unknown boolean: %d.\n", gprintVar(getConstraints()[i]->getAtom()));
			return false;
		}
	}
	return true;
}

vector<Lit> CPSolverData::getBoolChanges() const{
	vector<Lit> lits;
	for(int i=0; i<getConstraints().size(); i++){
		int boolvar = getConstraints()[i]->getBoolVar();
		BoolVar current = getSpace().getBoolVars()[boolvar];
		assert(history.size()>1);
		BoolVar prev = history[history.size()-2]->getBoolVars()[boolvar];
		if(current.min() == current.max() && prev.min() != prev.max()){
			lits.push_back(Lit(getConstraints()[i]->getAtom(), current.min()==0));
		}
	}
	return lits;
}

vector<TermIntVar> CPSolverData::convertToVars(const vector<int>& terms) const {
	vector<TermIntVar> set;
	for(vector<int>::const_iterator i=terms.begin(); i<terms.end(); i++){
		set.push_back(convertToVar(*i));
	}
	return set;
}

TermIntVar CPSolverData::convertToVar(int term) const {
	for(vector<TermIntVar>::const_iterator j=getTerms().begin(); j<getTerms().end(); j++){
		if((*j).operator ==(term)){
			return *j;
		}
	}
	throw idpexception("An integer variable occurred without having been created.\n");
}
