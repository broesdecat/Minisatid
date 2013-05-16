/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "modules/cpsolver/CPSolverData.hpp"
#include "modules/cpsolver/Constraint.hpp"
#include "modules/cpsolver/CPScript.hpp"
#include "modules/cpsolver/CPUtils.hpp"
#include "external/utils/ContainerUtils.hpp"

using namespace std;
using namespace MinisatID;
using namespace Gecode;

CPSolverData::CPSolverData(){
	history.push_back(new CPScript());
}

CPSolverData::~CPSolverData(){
	deleteList(reifconstraints);
	deleteList(nonreifconstraints);
	deleteList(history);
}

void CPSolverData::addSpace(){
	history.push_back(static_cast<CPScript*>(getSpace().clone()));
}

void CPSolverData::removeSpace(){
	auto old = history.back();
	history.pop_back();
	delete old;
}

void CPSolverData::replaceLastWith(CPScript* space){
	auto old = history.back();
	history.pop_back();
	delete old;
	history.push_back(space);
}

void CPSolverData::addTerm(const TermIntVar& var){
	terms[var.getID()]=var;
}

void CPSolverData::addReifConstraint(ReifiedConstraint* c) {
	reifconstraints[c->getHead()]=c;
}

vector<TermIntVar> CPSolverData::convertToVars(const vector<VarID>& terms) const {
	std::vector<TermIntVar> set;
	for(auto term:terms){
		set.push_back(convertToVar(term));
	}
	return set;
}

TermIntVar CPSolverData::convertToVar(VarID term) const {
	auto it = getTerms().find(term);
	if(it==getTerms().cend()){
		stringstream ss;
		ss <<"The integer variable " <<term.id <<" occurred without having been created.\n";
		throw idpexception(ss.str());
	}
	return it->second;

}
