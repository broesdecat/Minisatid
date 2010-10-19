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

#include "solvers/external/ExternalInterface.hpp"

#include <cstdlib>
#include <vector>
#include <tr1/memory>
#include <algorithm>

using namespace std;
using namespace MinisatID;

SolverInterface::SolverInterface(ECNF_mode modes):
		_modes(modes), maxnumber(0),
		origtocontiguousatommapper(),
		contiguoustoorigatommapper(),
		currentsolution(NULL),
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

InternSol* SolverInterface::mapToInternSol(Solution* sol){
	vec<Lit> ass;
	checkLits(sol->getAssumptions(), ass);
	InternSol* insol = new InternSol(sol->getPrint(), sol->getSave(), sol->getNbModelsToFind(), ass);
	return insol;
}

void PropositionalSolver::addForcedChoices(const vector<Literal> lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	getSolver()->addForcedChoices(ll);
}

bool SolverInterface::finishParsing(){
	return getSolver()->finishParsing();
}

bool SolverInterface::simplify(){
	return getSolver()->simplify();
}

void SolverInterface::solve(Solution* sol){
	currentsolution = sol;

	//Map to internal solution
	InternSol* insol = mapToInternSol(currentsolution);

	getSolver()->solve(insol);

	delete insol;

	if(currentsolution->modelCount()==0){
		fprintf(getRes()==NULL?stdout:getRes(), "UNSAT\n");
		if(modes().verbosity>=1){
			printf("UNSATISFIABLE\n");
		}
	}

	currentsolution = NULL;
}

void SolverInterface::addModel(const vec<Lit>& model){
	//Translate into original vocabulary
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); j++){
		if(!wasInput(var(model[j]))){ //was not part of the input
			continue;
		}
		outmodel.push_back(getOrigLiteral(model[j]));
	}
	sort(outmodel.begin(), outmodel.end());

	assert(currentsolution!=NULL);
	currentsolution->addModel(outmodel);

	if(currentsolution->getPrint()){
		if(currentsolution->getModels().size()==1){	//First model found
			fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
			if(modes().verbosity>=1){
				printf("SATISFIABLE\n");
			}
		}

		//Effectively print the model
		bool start = true;
		for (vector<Literal>::const_iterator i = outmodel.begin(); i < outmodel.end(); i++){
			fprintf(getRes()==NULL?stdout:getRes(), "%s%s%d", start ? "" : " ", ((*i).getSign()) ? "-" : "", (*i).getAtom().getValue());
			start = false;
		}
		fprintf(getRes()==NULL?stdout:getRes(), " 0\n");
	}
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
bool PropositionalSolver::addSet(int id, const vector<WLtuple>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<WLtuple>::const_iterator i=lws.begin(); i<lws.end(); i++){
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

void ModalSolver::addVar(vsize modid, Atom v){
	getSolver()->addVar(modid, checkAtom(v));
}

bool ModalSolver::addClause(vsize modid, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(modid, ll);
}

bool ModalSolver::addRule(vsize modid, bool conj, Literal head, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(modid, conj, checkLit(head), ll);
}

bool ModalSolver::addSet(vsize modid, int id, vector<Literal>& lits, vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(modid, id, ll, w);
}

//Might be implemented more efficiently in the future
bool ModalSolver::addSet(vsize modid, int id, vector<WLtuple>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<WLtuple>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	vec<Lit> ll;
	checkLits(lits, ll);

	return addSet(modid, id, lits, weights);
}

bool ModalSolver::addAggrExpr(vsize modid, Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(modid, checkLit(head), setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool ModalSolver::addChild(vsize parent, vsize child, Literal head){
	return getSolver()->addChild(parent, child, checkLit(head));
}

bool ModalSolver::addAtoms(vsize modid, const vector<Atom>& atoms){
	vector<Var> aa;
	checkAtoms(atoms, aa);
	return getSolver()->addAtoms(modid, aa);
}
