/*
 * ExternalInterface.cpp
 *
 *  Created on: Jul 22, 2010
 *      Author: broes
 */

#include "solvers/ExternalInterface.hpp"
#include "solvers/solverfwd.hpp"

#include "solvers/PCSolver.hpp"

modindex getModIndex(modID modid){
	return (int)modid;
}

Var getVar(Atom atom){
	return atom.getValue()-1;
}

Atom getAtom(Var v){
	return Atom(v+1);
}

Lit getLit(Literal lit){
	return Lit(getVar(lit.getAtom()), lit.getSign());
}

Literal getLiteral(Lit lit){
	return Literal(getAtom(var(lit)), sign(lit));
}

PropositionalSolver::PropositionalSolver(ECNF_mode modes)
		:SolverInterface(modes), impl(new PCSolver(modes)){

}

PropositionalSolver::~PropositionalSolver(){
	delete impl;
}

void PropositionalSolver::setNbModels(int nb){
	getSolver()->setNbModels(nb);
}

void PropositionalSolver::setRes(FILE* f){
	getSolver()->setRes(f);
}

bool PropositionalSolver::simplify(){
	return getSolver()->simplify();
}

bool PropositionalSolver::solve(){
	return getSolver()->solve();
}

bool PropositionalSolver::solve(vector<vector<int> >& models){
	return getSolver()->solve(models);
}

Atom PropositionalSolver::newVar(){
	return getAtom(getSolver()->newVar());
}

void PropositionalSolver::addVar(Atom v){
	getSolver()->addVar(getVar(v));
}

bool PropositionalSolver::addClause(vector<Literal>& lits){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addClause(ll);
}

bool PropositionalSolver::addRule(bool conj, vector<Literal>& lits){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addRule(conj, ll);
}

bool PropositionalSolver::addSet(int id, vector<Literal>& lits){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addSet(id, ll);
}

bool PropositionalSolver::addSet(int id, vector<Literal>& lits, const vector<Weight>& w){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addSet(id, ll, w);
}

bool PropositionalSolver::addAggrExpr(Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	return getSolver()->addAggrExpr(getLit(head), setid, bound, lower, type, defined);
}

bool PropositionalSolver::finishParsing	(){
	return getSolver()->finishParsing();
}

bool PropositionalSolver::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addMinimize(ll, subsetmnmz);
}

bool PropositionalSolver::addSumMinimize(const Atom head, const int setid){
    return getSolver()->addSumMinimize(getVar(head), setid);
}

bool PropositionalSolver::addIntVar(int groundname, int min, int max){
	return getSolver()->addIntVar(groundname, min, max);
}

bool PropositionalSolver::addCPSum(Literal head, vector<int> termnames, MINISAT::EqType rel, int bound){
	return getSolver()->addCPSum(getLit(head), termnames, rel, bound);
}

bool PropositionalSolver::addCPSum(Literal head, vector<int> termnames, vector<int> mult, MINISAT::EqType rel, int bound){
	return getSolver()->addCPSum(getLit(head), termnames, mult, rel, bound);
}

bool PropositionalSolver::addCPSumVar(Literal head, vector<int> termnames, MINISAT::EqType rel, int rhstermname){
	return getSolver()->addCPSum(getLit(head), termnames, rel, rhstermname);
}

bool PropositionalSolver::addCPSumVar(Literal head, vector<int> termnames, vector<int> mult, MINISAT::EqType rel, int rhstermname){
	return getSolver()->addCPSum(getLit(head), termnames, mult, rel, rhstermname);
}

bool PropositionalSolver::addCPCount(vector<int> termnames, int value, MINISAT::EqType rel, int rhstermname){
	return getSolver()->addCPCount(termnames, value, rel, rhstermname);
}


/****************
 * MODEL SOLVER *
 ****************/

ModalSolver::ModalSolver(ECNF_mode modes):SolverInterface(modes), impl(new ModSolverData(modes)){

}

ModalSolver::~ModalSolver(){
	delete impl;
}

void ModalSolver::setNbModels(int nb){
	getSolver()->setNbModels(nb);
}

void ModalSolver::setRes(FILE* f){
	getSolver()->setRes(f);
}

void ModalSolver::addVar(modID modid, Atom v){
	getSolver()->addVar(getModIndex(modid), getVar(v));
}

bool ModalSolver::addClause(modID modid, vector<Literal>& lits){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addClause(getModIndex(modid), ll);
}

bool ModalSolver::addRule(modID modid, bool conj, vector<Literal>& lits){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addRule(getModIndex(modid), conj, ll);
}

bool ModalSolver::addSet(modID modid, int id, vector<Literal>& lits, vector<Weight>& w){
	vec<Lit> ll;
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(getLit(*i));
	}
	return getSolver()->addSet(getModIndex(modid), id, ll, w);
}

bool ModalSolver::addAggrExpr(modID modid, Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	return getSolver()->addAggrExpr(getModIndex(modid), getLit(head), setid, bound, lower, type, defined);
}

bool ModalSolver::finishParsing	(){
	return getSolver()->finishParsing();
}

bool ModalSolver::simplify(){
	return getSolver()->simplify();
}

bool ModalSolver::solve(){
	return getSolver()->solve();
}

//Add information for hierarchy
bool ModalSolver::addChild(modID parent, modID child, Literal head){
	return getSolver()->addChild(getModIndex(parent), getModIndex(child), getLit(head));
}

void ModalSolver::addAtoms(modID modid, const vector<Atom>& atoms){
	vector<Var> ll;
	for(vector<Atom>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		ll.push_back(getVar(*i));
	}
	getSolver()->addAtoms(getModIndex(modid), ll);
}
