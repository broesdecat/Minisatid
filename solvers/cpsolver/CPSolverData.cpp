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

#include "solvers/cpsolver/CPSolverData.hpp"
#include "solvers/utils/Utils.hpp"

using namespace CP;

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
	/*reportf("BACKTRACKING SPACES");
	for(int i=0; i<history.size(); i++){
		reportf("SPACE");
		cout <<*history[i] <<endl;
	}*/

	CPScript* old = history.back();
	history.pop_back();
	delete old;
}

void CPSolverData::replaceLastWith(CPScript* space){
	CPScript* old = history.back();
	history.pop_back();
	delete old;
	history.push_back(space);
}

/*vector<Lit> CPSolverData::getBoolChanges() const{
	vector<Lit> lits;
	for(vreifconstrptr::const_iterator i=getReifConstraints().begin(); i<getReifConstraints().end(); i++){
		BoolVar current = (*i)->getBoolVar(getSpace());
		assert(history.size()>1);
		BoolVar prev = (*i)->getBoolVar(*history[history.size()-2]);
		if(current.min() == current.max() && prev.min() != prev.max()){
			lits.push_back(mkLit((*i)->getAtom(), current.min()==0));
		}
	}
	return lits;
}*/

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
