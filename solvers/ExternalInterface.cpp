/*
 * ExternalInterface.cpp
 *
 *  Created on: Jul 22, 2010
 *      Author: broes
 */

#include "solvers/ExternalInterface.hpp"

#include <cstdlib>
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

Literal getLiteral(Lit lit){
	return Literal(getAtom(var(lit)), sign(lit));
}

Var SolverInterface::checkAtom(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception("Variables can only be numbered starting from 1.");
	}
	unordered_map<int, int>::const_iterator i = origtocontiguousatommapper.find(getVar(atom));
	if(i==origtocontiguousatommapper.end()){
		//reportf("%d mapped to %d\n", getVar(atom), freeindex);
		origtocontiguousatommapper.insert(pair<int, int>(getVar(atom), freeindex));
		contiguoustoorigatommapper.insert(pair<int, int>(freeindex, getVar(atom)));
		return freeindex++;
	}else{
		return (*i).second;
	}
}

Lit SolverInterface::checkLit(const Literal& lit){
	return Lit(checkAtom(lit.getAtom()), lit.getSign());
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
	unordered_map<int, int>::const_iterator atom = contiguoustoorigatommapper.find(nonindexatom.getValue());
	assert(atom!=contiguoustoorigatommapper.end());
	int origatom = (*atom).second;
	return Literal(origatom, sign(l));
}


/************
 * PROP SOLVER
 */

PropositionalSolver::PropositionalSolver(ECNF_mode modes)
		:SolverInterface(modes), impl(new PCSolver(modes)){

}

PropositionalSolver::~PropositionalSolver(){
	delete impl;
}

void PropositionalSolver::setNbModels(int nb){
	getSolver()->setNbModels(nb);
}

bool PropositionalSolver::simplify(){
	return getSolver()->simplify();
}

bool PropositionalSolver::solve(){
	vector<vector<Literal> > models;
	return solve(models);
}

bool PropositionalSolver::solve(vector<vector<Literal> >& models){
	vector<vector<int> > varmodels; //int-format literals, INDEXED!
	bool result = getSolver()->solve(varmodels);

	if (varmodels.size()==1) {
		fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
		if(modes().verbosity>=1){
			printf("SATISFIABLE\n");
		}
	}

	if(result){
		//Translate into original vocabulary
		for(vector<vector<int> >::const_iterator model=varmodels.begin(); model<varmodels.end(); model++){
			vector<Literal> outmodel;
			for(vector<int>::const_iterator lit=(*model).begin(); lit<(*model).end(); lit++){
				//TODO should move more inside
				if(wasInput(abs(*lit))){ //was not part of the input
					continue;
				}
				outmodel.push_back(getOrigLiteral(Lit(abs(*lit), (*lit)<0)));
			}
			models.push_back(outmodel);
			printModel(outmodel);
			//TODO at the moment, all models are calculated, afterwards they are printed.
			//it would be nice to print them one by one when they are found
		}
	}

	return result;
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

bool PropositionalSolver::addRule(bool conj, Literal head, vector<Literal>& lits){
	Lit newhead = checkLit(head);
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(conj, newhead, ll);
}

bool PropositionalSolver::addSet(int id, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll);
}

//Might be implemented more efficiently in the future
bool PropositionalSolver::addSet(int id, vector<LW>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<LW>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	vector<Literal> ll;
	checkLits(lits, ll);

	return addSet(id, ll, weights);
}

bool PropositionalSolver::addSet(int id, vector<Literal>& lits, const vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll, w);
}

bool PropositionalSolver::addAggrExpr(Literal head, int setid, Weight bound, bool lower, AggrType type, bool defined){
	checkLit(head);
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
	Var newhead = checkAtom(head);
    return getSolver()->addSumMinimize(newhead, setid);
}

bool PropositionalSolver::addIntVar(int groundname, int min, int max){
	return getSolver()->addIntVar(groundname, min, max);
}

bool PropositionalSolver::addCPBinaryRel(Literal head, int groundname, MINISAT::EqType rel, int bound){
	return getSolver()->addCPBinaryRel(checkLit(head), groundname, rel, bound);
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

void PropositionalSolver::printModel(const vector<Literal>& model) const{
	int nvars = (int)getSolver()->nVars();
	for (int i = 0; i < nvars; i++){
		//TODO check that this was not necessary?
		//if (model[i] != l_Undef){
			fprintf(getRes()==NULL?stdout:getRes(), "%s%s%d", (i == 0) ? "" : " ", (model[i].getSign()) ? "-" : "", i + 1);
		//}
	}
	fprintf(getRes()==NULL?stdout:getRes(), " 0\n");
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

bool ModalSolver::solve(){
	return getSolver()->solve();
}

//Add information for hierarchy
bool ModalSolver::addChild(modID parent, modID child, Literal head){
	return getSolver()->addChild(getModIndex(parent), getModIndex(child), checkLit(head));
}

void ModalSolver::addAtoms(modID modid, const vector<Atom>& atoms){
	vector<Var> aa;
	checkAtoms(atoms, aa);
	getSolver()->addAtoms(getModIndex(modid), aa);
}
