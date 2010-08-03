/*
 * CPSolverData.cpp
 *
 *  Created on: Jul 27, 2010
 *      Author: broes
 */

#include "solvers/cpsolver/CPSolverData.hpp"
#include "solvers/utils/Utils.hpp"

using namespace CP;

CPSolverData::CPSolverData(){
	history.push_back(new CPScript());
}

CPSolverData::~CPSolverData(){
	deleteList(constraints);
}

bool CPSolverData::allBooleansKnown() const{
	for(vconstrptr::const_iterator i=getConstraints().begin(); i<getConstraints().end(); i++){
		if(!(*i)->isAssigned(getSpace())){
			reportf("Unknown boolean: %d.\n", gprintVar((*i)->getAtom()));
			return false;
		}
	}
	return true;
}

vector<Lit> CPSolverData::getBoolChanges() const{
	vector<Lit> lits;
	for(vconstrptr::const_iterator i=getConstraints().begin(); i<getConstraints().end(); i++){
		BoolVar current = (*i)->getBoolVar(getSpace());
		assert(history.size()>1);
		BoolVar prev = (*i)->getBoolVar(*history[history.size()-2]);
		if(current.min() == current.max() && prev.min() != prev.max()){
			lits.push_back(mkLit((*i)->getAtom(), current.min()==0));
		}
	}
	return lits;
}

vector<TermIntVar> CPSolverData::convertToVars(const vector<int>& terms) const {
	vtiv set;
	for(vector<int>::const_iterator i=terms.begin(); i<terms.end(); i++){
		set.push_back(convertToVar(*i));
	}
	return set;
}

TermIntVar CPSolverData::convertToVar(int term) const {
	for(vtiv::const_iterator j=getTerms().begin(); j<getTerms().end(); j++){
		if((*j).operator ==(term)){
			return *j;
		}
	}
	throw idpexception("An integer variable occurred without having been created.\n");
}
