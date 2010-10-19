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

/*
 * ExternalInterface.cpp
 *
 *  Created on: Jul 22, 2010
 *      Author: broes
 */

#include "solvers/external/ExternalInterface.hpp"

#include <cstdlib>
#include <map>
#include <vector>
#include <tr1/memory>
#include "solvers/pcsolver/PCSolver.hpp"
#include "solvers/modsolver/SOSolverHier.hpp"

#include <algorithm>

using namespace std;
using namespace MinisatID;

modindex getModIndex(modID modid){
       return (int)modid;
}

SolverInterface::SolverInterface(ECNF_mode modes):
		_modes(modes), maxnumber(0),
		origtocontiguousatommapper(),
		contiguoustoorigatommapper(),
		firstmodel(true){
}

Atom SolverInterface::getOrigAtom(const Var& v) const{
	if(modes().remap){
		atommap::const_iterator atom = contiguoustoorigatommapper.find(v);
		assert(atom!=contiguoustoorigatommapper.end());
		//reportf("Retrieving literal "); gprintLit(l); reportf("mapped as %d to %d\n", (*atom).first, (*atom).second);
		int origatom = (*atom).second;
		return Atom(origatom);
	}else{
		return Atom(v+1);
	}
}

Var SolverInterface::checkAtom(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception("Variables can only be numbered starting from 1.\n");
	}
	if(modes().remap){
		atommap::const_iterator i = origtocontiguousatommapper.find(atom.getValue());
		if(i==origtocontiguousatommapper.end()){
			//reportf("%d mapped to %d\n", atom.getValue(), freeindex);
			origtocontiguousatommapper.insert(pair<int, int>(atom.getValue(), maxnumber));
			contiguoustoorigatommapper.insert(pair<int, int>(maxnumber, atom.getValue()));
			return maxnumber++;
		}else{
			return (*i).second;
		}
	}else{
		if(atom.getValue()>maxnumber){
			maxnumber = atom.getValue();
		}
		return atom.getValue()-1;
	}
}

Literal SolverInterface::getOrigLiteral(const Lit& l) const{
	assert(var(l)>-1);
	return Literal(getOrigAtom(var(l)), sign(l));
}

Lit SolverInterface::checkLit(const Literal& lit){
	return mkLit(checkAtom(lit.getAtom()), lit.getSign());
}

void SolverInterface::checkLits(const vector<Literal>& lits, vec<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(checkLit(*i));
	}
}

void SolverInterface::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkLit(*i));
	}
}

void SolverInterface::checkAtoms(const vector<Atom>& lits, vector<Var>& ll){
	for(vector<Atom>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkAtom(*i));
	}
}

void PropositionalSolver::addForcedChoices(const vector<Literal> lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	getSolver()->addForcedChoices(ll);
}

/*bool SolverInterface::solveprintModels(int nbmodels){
	bool result = getSolver()->solveprintModels(nbmodels);

	if(firstmodel && result){
		fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
		if(modes().verbosity>=1){
			printf("SATISFIABLE\n");
		}
		firstmodel = false;
	} else if(!result){
		fprintf(getRes()==NULL?stdout:getRes(), "UNSAT\n");
		if(modes().verbosity>=1){
			printf("UNSATISFIABLE\n");
		}
	}

	return result;
}

bool SolverInterface::solvefindModels(int nbmodels, vector<vector<Literal> >& models){
	vec<vec<Lit> > varmodels; //int-format literals, INDEXED!
	bool result = getSolver()->solvefindModels(nbmodels, varmodels);

	if(firstmodel && result){
		fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
		if(modes().verbosity>=1){
			printf("SATISFIABLE\n");
		}
		firstmodel = false;
	} else if(!result){
		fprintf(getRes()==NULL?stdout:getRes(), "UNSAT\n");
		if(modes().verbosity>=1){
			printf("UNSATISFIABLE\n");
		}
	}

	//Translate into original vocabulary
	for(int i=0; i<varmodels.size(); i++){
		vector<Literal> outmodel;
		for(int j=0; j<varmodels[i].size(); j++){
			if(!wasInput(var(varmodels[i][j]))){ //was not part of the input
				continue;
			}
			outmodel.push_back(getOrigLiteral(varmodels[i][j]));
		}
		sort(outmodel.begin(), outmodel.end());
		models.push_back(outmodel);
	}

	return result;

	return getSolver()->solvefindModels(nbmodels, models);
}*/

bool SolverInterface::finishParsing(){
	return getSolver()->finishParsing();
}

bool SolverInterface::simplify(){

}

void SolverInterface::solve(Solution* sol){

}

void SolverInterface::printModel(const vec<Lit>& model){
	if(firstmodel){
		fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
		if(modes().verbosity>=1){
			printf("SATISFIABLE\n");
		}
		firstmodel = false;
	}

	//Translate into original vocabulary
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); j++){
		if(!wasInput(var(model[j]))){ //was not part of the input
			continue;
		}
		outmodel.push_back(getOrigLiteral(model[j]));
	}
	sort(outmodel.begin(), outmodel.end());
	//Effectively print the model
	bool start = true;
	for (vector<Literal>::const_iterator i = outmodel.begin(); i < outmodel.end(); i++){
		fprintf(getRes()==NULL?stdout:getRes(), "%s%s%d", start ? "" : " ", ((*i).getSign()) ? "-" : "", (*i).getAtom().getValue());
		start = false;
	}
	fprintf(getRes()==NULL?stdout:getRes(), " 0\n");
}

///////
// PROP SOLVER
 ///////

PropositionalSolver::PropositionalSolver(ECNF_mode modes)
		:SolverInterface(modes), solver(new PCSolver(modes)){
	getSolver()->setParent(this);
}

PropositionalSolver::~PropositionalSolver(){
	delete solver;
}

PCSolver* PropositionalSolver::getSolver() const { return solver; }

void PropositionalSolver::addVar(Atom v){
	Var newv = checkAtom(v);
	getSolver()->addVar(newv);
}

bool PropositionalSolver::addClause(vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(ll);
}

bool PropositionalSolver::addRule(bool conj, Literal head, const vector<Literal>& lits){
	Lit newhead = checkLit(head);
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(conj, newhead, ll);
}

bool PropositionalSolver::addSet(int id, const vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll);
}

//Might be implemented more efficiently in the future
bool PropositionalSolver::addSet(int id, const vector<LW>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<LW>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	return addSet(id, lits, weights);
}

bool PropositionalSolver::addSet(int id, const vector<Literal>& lits, const vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll, w);
}

bool PropositionalSolver::addAggrExpr(Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(checkLit(head), setid, bound, sign, type, sem);
}

bool PropositionalSolver::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addMinimize(ll, subsetmnmz);
}

bool PropositionalSolver::addSumMinimize(const Atom head, const int setid){
    return getSolver()->addSumMinimize(checkAtom(head), setid);
}

bool PropositionalSolver::addIntVar(int groundname, int min, int max){
	return getSolver()->addIntVar(groundname, min, max);
}

bool PropositionalSolver::addCPBinaryRel(Literal head, int groundname, EqType rel, int bound){
	return getSolver()->addCPBinaryRel(checkLit(head), groundname, rel, bound);
}

bool PropositionalSolver::addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2){
	return getSolver()->addCPBinaryRelVar(checkLit(head), groundname, rel, groundname2);
}

bool PropositionalSolver::addCPSum(Literal head, const vector<int>& termnames, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, bound);
}

bool PropositionalSolver::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, bound);
}

bool PropositionalSolver::addCPSumVar(Literal head, const vector<int>& termnames, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, rhstermname);
}

bool PropositionalSolver::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, rhstermname);
}

bool PropositionalSolver::addCPCount(const vector<int>& termnames, int value, EqType rel, int rhstermname){
	return getSolver()->addCPCount(termnames, value, rel, rhstermname);
}

bool PropositionalSolver::addCPAlldifferent(const vector<int>& termnames){
	return getSolver()->addCPAlldifferent(termnames);
}

void PropositionalSolver::printStatistics() const {
	getSolver()->printStatistics();
}

///////
// MODEL SOLVER
///////

ModalSolver::ModalSolver(ECNF_mode modes):SolverInterface(modes), solver(new ModSolverData(modes)){
	getSolver()->setParent(this);
}

ModalSolver::~ModalSolver(){
	delete solver;
}

ModSolverData* ModalSolver::getSolver() const { return solver; }

void ModalSolver::addVar(modID modid, Atom v){
	getSolver()->addVar(getModIndex(modid), checkAtom(v));
}

bool ModalSolver::addClause(modID modid, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(getModIndex(modid), ll);
}

bool ModalSolver::addRule(modID modid, bool conj, Literal head, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(getModIndex(modid), conj, checkLit(head), ll);
}

bool ModalSolver::addSet(modID modid, int id, vector<Literal>& lits, vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(getModIndex(modid), id, ll, w);
}

//Might be implemented more efficiently in the future
bool ModalSolver::addSet(modID modid, int id, vector<LW>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<LW>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	vec<Lit> ll;
	checkLits(lits, ll);

	return addSet(getModIndex(modid), id, lits, weights);
}

bool ModalSolver::addAggrExpr(modID modid, Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(getModIndex(modid), checkLit(head), setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool ModalSolver::addChild(modID parent, modID child, Literal head){
	return getSolver()->addChild(getModIndex(parent), getModIndex(child), checkLit(head));
}

bool ModalSolver::addAtoms(modID modid, const vector<Atom>& atoms){
	vector<Var> aa;
	checkAtoms(atoms, aa);
	return getSolver()->addAtoms(getModIndex(modid), aa);
}
