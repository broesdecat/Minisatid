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

WrappedLogicSolver::WrappedLogicSolver(ECNF_mode modes):
		_modes(modes), maxnumber(0),
		origtocontiguousatommapper(),
		contiguoustoorigatommapper(),
		firstmodel(true){
}

Atom WrappedLogicSolver::getOrigAtom(const Var& v) const{
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

Var WrappedLogicSolver::checkAtom(const Atom& atom){
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

Literal WrappedLogicSolver::getOrigLiteral(const Lit& l) const{
	assert(var(l)>-1);
	return Literal(getOrigAtom(var(l)), sign(l));
}

Lit WrappedLogicSolver::checkLit(const Literal& lit){
	return mkLit(checkAtom(lit.getAtom()), lit.getSign());
}

void WrappedLogicSolver::checkLits(const vector<Literal>& lits, vec<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(checkLit(*i));
	}
}

void WrappedLogicSolver::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkLit(*i));
	}
}

void WrappedLogicSolver::checkAtoms(const vector<Atom>& lits, vector<Var>& ll){
	for(vector<Atom>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkAtom(*i));
	}
}

void WrappedPCSolver::addForcedChoices(const vector<Literal> lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	getSolver()->addForcedChoices(ll);
}

bool WrappedLogicSolver::finishParsing(){
	return getSolver()->finishParsing();
}

bool WrappedLogicSolver::simplify(){
	return getSolver()->simplify();
}

bool WrappedLogicSolver::solve(Solution* sol){
	// Map to internal repr for assumptions
	vec<Lit> assumptions;
	checkLits(sol->getAssumptions(), assumptions);
	bool sat = getSolver()->solve(assumptions, sol);
	return sat;
}

void WrappedLogicSolver::addModel(const vec<Lit>& model, Solution* sol){
	//Translate into original vocabulary
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); j++){
		if(!wasInput(var(model[j]))){ //was not part of the input
			continue;
		}
		outmodel.push_back(getOrigLiteral(model[j]));
	}
	sort(outmodel.begin(), outmodel.end());

	assert(sol!=NULL);
	sol->addModel(outmodel);

	if(sol->getPrint()){
		if(sol->getNbModelsFound()==1){	//First model found
			fprintf(getRes()==NULL?stdout:getRes(), "SAT\n");
			if(modes().verbosity>=1){
				printf("SATISFIABLE\n");
			}
		}

		if(verbosity()>=1){
			report("| %4d model%s found                                                           |\n",
					sol->getNbModelsFound(), sol->getNbModelsFound() > 1 ? "s" : " ");
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

WrappedPCSolver::WrappedPCSolver(ECNF_mode modes)
		:WrappedLogicSolver(modes), solver(new PCSolver(modes, this)){
}

WrappedPCSolver::~WrappedPCSolver(){
	delete solver;
}

PCSolver* WrappedPCSolver::getSolver() const { return solver; }

/*void WrappedPCSolver::addVar(Atom v){
	Var newv = checkAtom(v);
	getSolver()->addVar(newv);
}*/

bool WrappedPCSolver::addClause(vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(ll);
}

bool WrappedPCSolver::addRule(bool conj, Literal head, const vector<Literal>& lits){
	Lit newhead = checkLit(head);
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(conj, newhead, ll);
}

bool WrappedPCSolver::addSet(int id, const vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll);
}

//Might be implemented more efficiently in the future
bool WrappedPCSolver::addSet(int id, const vector<WLtuple>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<WLtuple>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	return addSet(id, lits, weights);
}

bool WrappedPCSolver::addSet(int id, const vector<Literal>& lits, const vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll, w);
}

bool WrappedPCSolver::addAggrExpr(Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(checkLit(head), setid, bound, sign, type, sem);
}

bool WrappedPCSolver::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addMinimize(ll, subsetmnmz);
}

bool WrappedPCSolver::addSumMinimize(const Atom head, const int setid){
    return getSolver()->addSumMinimize(checkAtom(head), setid);
}

bool WrappedPCSolver::addIntVar(int groundname, int min, int max){
	return getSolver()->addIntVar(groundname, min, max);
}

bool WrappedPCSolver::addCPBinaryRel(Literal head, int groundname, EqType rel, int bound){
	return getSolver()->addCPBinaryRel(checkLit(head), groundname, rel, bound);
}

bool WrappedPCSolver::addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2){
	return getSolver()->addCPBinaryRelVar(checkLit(head), groundname, rel, groundname2);
}

bool WrappedPCSolver::addCPSum(Literal head, const vector<int>& termnames, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, bound);
}

bool WrappedPCSolver::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, bound);
}

bool WrappedPCSolver::addCPSumVar(Literal head, const vector<int>& termnames, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, rhstermname);
}

bool WrappedPCSolver::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, rhstermname);
}

bool WrappedPCSolver::addCPCount(const vector<int>& termnames, int value, EqType rel, int rhstermname){
	return getSolver()->addCPCount(termnames, value, rel, rhstermname);
}

bool WrappedPCSolver::addCPAlldifferent(const vector<int>& termnames){
	return getSolver()->addCPAlldifferent(termnames);
}

void WrappedPCSolver::printStatistics() const {
	getSolver()->printStatistics();
}

///////
// MODEL SOLVER
///////

WrappedSOSolver::WrappedSOSolver(ECNF_mode modes):
		WrappedLogicSolver(modes), solver(new SOSolver(modes, this)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete solver;
}

SOSolver* WrappedSOSolver::getSolver() const { return solver; }

/*void WrappedSOSolver::addVar(vsize modid, Atom v){
	getSolver()->addVar(modid, checkAtom(v));
}*/

bool WrappedSOSolver::addClause(vsize modid, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(modid, ll);
}

bool WrappedSOSolver::addRule(vsize modid, bool conj, Literal head, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(modid, conj, checkLit(head), ll);
}

bool WrappedSOSolver::addSet(vsize modid, int id, vector<Literal>& lits, vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(modid, id, ll, w);
}

//Might be implemented more efficiently in the future
bool WrappedSOSolver::addSet(vsize modid, int id, vector<WLtuple>& lws){
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

bool WrappedSOSolver::addAggrExpr(vsize modid, Literal head, int setid, Weight bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(modid, checkLit(head), setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool WrappedSOSolver::addChild(vsize parent, vsize child, Literal head){
	return getSolver()->addChild(parent, child, checkLit(head));
}

bool WrappedSOSolver::addAtoms(vsize modid, const vector<Atom>& atoms){
	vector<Var> aa;
	checkAtoms(atoms, aa);
	return getSolver()->addAtoms(modid, aa);
}
