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

void CPSolverData::removeSpace(int untillevel){
	/*reportf("BACKTRACKING SPACES");
	for(int i=0; i<history.size(); i++){
		reportf("SPACE");
		cout <<*history[i] <<endl;
	}*/

	while(history.size()>untillevel+1){
		CPScript* old = history.back();
		history.pop_back();
		delete old;
	}
}

void CPSolverData::replaceLastWith(CPScript* space){
	CPScript* old = history.back();
	history.pop_back();
	delete old;
	history.push_back(space);
}

/*vector<Lit> CPSolverData::getBoolChanges() const{
	vector<Lit> lits;
	for(vreifconstrptr::const_iterator i=getReifConstraints().cbegin(); i<getReifConstraints().cend(); i++){
		BoolVar current = (*i)->getBoolVar(getSpace());
		assert(history.size()>1);
		BoolVar prev = (*i)->getBoolVar(*history[history.size()-2]);
		if(current.min() == current.max() && prev.min() != prev.max()){
			lits.push_back(mkLit((*i)->getAtom(), current.min()==0));
		}
	}
	return lits;
}*/

void CPSolverData::addTerm(const TermIntVar& var){
	terms.push_back(var);
}

vector<TermIntVar> CPSolverData::convertToVars(const vector<uint>& terms) const {
	vtiv set;
	for(vector<uint>::const_iterator i=terms.cbegin(); i<terms.cend(); i++){
		set.push_back(convertToVar(*i));
	}
	return set;
}

TermIntVar CPSolverData::convertToVar(uint term) const {
	for(vtiv::const_iterator j=getTerms().cbegin(); j<getTerms().cend(); j++){
		if((*j).operator ==(term)){
			return *j;
		}
	}
	stringstream ss;
	ss <<"The integer variable " <<term <<" occurred without having been created.\n";
	throw idpexception(ss.str());
}
