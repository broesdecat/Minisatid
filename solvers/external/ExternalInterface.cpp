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
#include "solvers/pcsolver/PCSolver.hpp"
#include "solvers/modsolver/SOSolverHier.hpp"

#include <algorithm>

modindex getModIndex(modID modid){
	return (int)modid;
}

Var getVar(Atom atom){
	return atom.getValue()-1;
}

Atom getAtom(Var v){
	return Atom(v+1);
}

Literal getLiteral(Lit lit){
	return Literal(getAtom(var(lit)), sign(lit));
}

Var SolverInterface::checkAtom(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception("Variables can only be numbered starting from 1.\n");
	}
	atommap::const_iterator i = origtocontiguousatommapper.find(atom.getValue());
	if(i==origtocontiguousatommapper.end()){
		//reportf("%d mapped to %d\n", atom.getValue(), freeindex);
		origtocontiguousatommapper.insert(pair<int, int>(atom.getValue(), freeindex));
		contiguoustoorigatommapper.insert(pair<int, int>(freeindex, atom.getValue()));
		return freeindex++;
	}else{
		return (*i).second;
	}
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

void SolverInterface::checkLits(const vector<Literal>& lits, vector<Literal>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(getLiteral(checkLit(*i)));
	}
}

void SolverInterface::checkAtoms(const vector<Atom>& lits, vector<Var>& ll){
	for(vector<Atom>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkAtom(*i));
	}
}

Literal SolverInterface::getOrigLiteral(const Lit& l) const{
	Atom nonindexatom = getAtom(abs(var(l)));
	atommap::const_iterator atom = contiguoustoorigatommapper.find(getVar(nonindexatom));
	assert(atom!=contiguoustoorigatommapper.end());
	//reportf("Retrieving literal "); gprintLit(l); reportf("mapped as %d to %d\n", (*atom).first, (*atom).second);
	int origatom = (*atom).second;
	return Literal(origatom, sign(l));
}

template <class T>
bool SolverInterface2<T>::solve(){
	vector<vector<Literal> > models;
	return solve(models);
}

template <class T>
bool SolverInterface2<T>::solve(vector<vector<Literal> >& models){
	vec<vec<Lit> > varmodels; //int-format literals, INDEXED!
	bool result = getSolver()->solve(varmodels);

	if (result) {
		fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
		if(modes().verbosity>=1){
			printf("SATISFIABLE\n");
		}
	}else{
		fprintf(getRes()==NULL?stdout:getRes(), "UNSAT\n");
		if(modes().verbosity>=1){
			printf("UNSATISFIABLE\n");
		}
	}

	if(result){
		//Translate into original vocabulary
		for(int i=0; i<varmodels.size(); i++){
			vector<Literal> outmodel;
			for(int j=0; j<varmodels[i].size(); j++){
				//TODO should move more inside
				if(!wasInput(var(varmodels[i][j]))){ //was not part of the input
					continue;
				}
				outmodel.push_back(getOrigLiteral(varmodels[i][j]));
			}
			sort(outmodel.begin(), outmodel.end());
			models.push_back(outmodel);
			printModel(outmodel);
			//TODO at the moment, all models are calculated, afterwards they are printed.
			//it would be nice to print them one by one when they are found
		}
	}

	return result;
}

/***************
 * PROP SOLVER *
 ***************/

PropositionalSolver::PropositionalSolver(ECNF_mode modes)
		:SolverInterface2<PCSolver>(modes, new PCSolver(modes)){

}

PropositionalSolver::~PropositionalSolver(){
}

void PropositionalSolver::setNbModels(int nb){
	getSolver()->setNbModels(nb);
}

bool PropositionalSolver::simplify(){
	return getSolver()->simplify();
}

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

bool PropositionalSolver::addAggrExpr(Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	return getSolver()->addAggrExpr(checkLit(head), setid, bound, lower, type, defined);
}

bool PropositionalSolver::finishParsing	(){
	return getSolver()->finishParsing();
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

bool PropositionalSolver::addCPBinaryRel(Literal head, int groundname, MINISAT::EqType rel, int bound){
	return getSolver()->addCPBinaryRel(checkLit(head), groundname, rel, bound);
}

bool PropositionalSolver::addCPBinaryRelVar(Literal head, int groundname, MINISAT::EqType rel, int groundname2){
	return getSolver()->addCPBinaryRelVar(checkLit(head), groundname, rel, groundname2);
}

bool PropositionalSolver::addCPSum(Literal head, const vector<int>& termnames, MINISAT::EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, bound);
}

bool PropositionalSolver::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, MINISAT::EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, bound);
}

bool PropositionalSolver::addCPSumVar(Literal head, const vector<int>& termnames, MINISAT::EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, rhstermname);
}

bool PropositionalSolver::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, MINISAT::EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, rhstermname);
}

bool PropositionalSolver::addCPCount(const vector<int>& termnames, int value, MINISAT::EqType rel, int rhstermname){
	return getSolver()->addCPCount(termnames, value, rel, rhstermname);
}

bool PropositionalSolver::addCPAlldifferent(const vector<int>& termnames){
	return getSolver()->addCPAlldifferent(termnames);
}

template <class T>
void SolverInterface2<T>::printModel(const vector<Literal>& model) const{
	bool start = true;
	for (vector<Literal>::const_iterator i = model.begin(); i < model.end(); i++){
		//TODO check that this was not necessary?
		//if (model[i] != l_Undef){
			fprintf(getRes()==NULL?stdout:getRes(), "%s%s%d", start ? "" : " ", ((*i).getSign()) ? "-" : "", (*i).getAtom().getValue());
			start = false;
		//}
	}
	fprintf(getRes()==NULL?stdout:getRes(), " 0\n");
}

/****************
 * MODEL SOLVER *
 ****************/

ModalSolver::ModalSolver(ECNF_mode modes):SolverInterface2<ModSolverData>(modes, new ModSolverData(modes)){

}

ModalSolver::~ModalSolver(){
}

void ModalSolver::setNbModels(int nb){
	getSolver()->setNbModels(nb);
}

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

bool ModalSolver::addAggrExpr(modID modid, Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	return getSolver()->addAggrExpr(getModIndex(modid), checkLit(head), setid, bound, lower, type, defined);
}

bool ModalSolver::finishParsing	(){
	return getSolver()->finishParsing();
}

bool ModalSolver::simplify(){
	return getSolver()->simplify();
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
