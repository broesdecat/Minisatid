//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

#include "external/InterfaceImpl.hpp"

#include <cstdlib>
#include <vector>
#include <tr1/memory>
#include <algorithm>

#include "parser/ResourceManager.hpp"
#include "utils/Print.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

///////
// REMAPPER
///////

Var Remapper::getVar(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception(getMinimalVarNumbering());
	}
	if(atom.getValue()>maxnumber){
		maxnumber = atom.getValue();
	}
	return atom.getValue()-1;
}

Literal Remapper::getLiteral(const Lit& lit){
	return Literal(var(lit)+1, sign(lit));
}

Var SmartRemapper::getVar(const Atom& atom){
	if(atom.getValue()<1){
		throw idpexception(getMinimalVarNumbering());
	}

	atommap::const_iterator i = origtocontiguousatommapper.find(atom.getValue());
	Var v = 0;
	if(i==origtocontiguousatommapper.end()){
		origtocontiguousatommapper.insert(pair<int, int>(atom.getValue(), maxnumber));
		contiguoustoorigatommapper.insert(pair<int, int>(maxnumber, atom.getValue()));
		v = maxnumber++;
	}else{
		v = (*i).second;
	}
	return v;
}

Literal SmartRemapper::getLiteral(const Lit& lit){
	atommap::const_iterator atom = contiguoustoorigatommapper.find(var(lit));
	assert(atom!=contiguoustoorigatommapper.end());
	int origatom = (*atom).second;
	return Literal(origatom, sign(lit));
}

///////
// PIMPL of External Interfaces
///////

WLSImpl::WLSImpl(const SolverOption& modes):
		optimization(false),
		state(INIT), _modes(modes),
		remapper(modes.remap?new SmartRemapper():new Remapper()),
		owntranslator(new Translator()),
		translator(*owntranslator) //Default translator is alwasy loaded
		{
}

WLSImpl::~WLSImpl(){
	if(owntranslator!=NULL){
		delete owntranslator;
	}
	delete remapper;
}

void WLSImpl::setTranslator(Translator& translator){
	translator = translator;
}

void WLSImpl::printLiteral(std::ostream& output, const Lit& l) const{
	getTranslator().printLiteral(output, getRemapper()->getLiteral(l));
}

void WLSImpl::printStatistics() const {
	getSolver()->printStatistics();
}

std::streambuf* WLSImpl::getRes() const {
	return getOutputBuffer();
}

Var WLSImpl::checkAtom(const Atom& atom){
	return getRemapper()->getVar(atom);
}

Lit WLSImpl::checkLit(const Literal& lit){
	return mkLit(checkAtom(lit.getAtom()), lit.hasSign());
}

void WLSImpl::checkLits(const vector<Literal>& lits, vec<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push(checkLit(*i));
	}
}

void WLSImpl::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkLit(*i));
	}
}

void WLSImpl::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll){
	for(vector<Atom>::const_iterator i=atoms.begin(); i<atoms.end(); i++){
		ll.push_back(checkAtom(*i));
	}
}

void WPCLSImpl::addForcedChoices(const vector<Literal> lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	getSolver()->addForcedChoices(ll);
}

bool WLSImpl::finishParsing(){
	printInitDataStart(modes().verbosity);

	bool present = true, unsat = false;
	double cpu_time = cpuTime(); //Start time
	getSolver()->finishParsing(present, unsat);
	state = PARSED;

	printInitDataEnd(modes().verbosity, cpuTime()-cpu_time, unsat);

	return !unsat;
}

bool WLSImpl::simplify(){
	printSimpStart(modes().verbosity);

	bool unsat = !getSolver()->simplify();
	state = SIMPLIFIED;

	printSimpEnd(modes().verbosity, unsat);

	return !unsat;
}

bool WLSImpl::solve(Solution* sol){
	bool unsat = false;

	if(!unsat && state==INIT){
		unsat = !finishParsing();
	}
	if(!unsat && state==PARSED){
		unsat = !simplify();
	}
	if(unsat){
		return false;
	}

	assert(state==SIMPLIFIED);
	printSolveStart(verbosity());

	// Map to internal repr for assumptions
	vec<Lit> assumptions;
	checkLits(sol->getAssumptions(), assumptions);
	bool sat = getSolver()->solve(assumptions, sol);

	if(sol->getSearch()){
		state = SOLVED;
	}

	if(modes().aspcomp3type!=ASPCOMP3_NOCOMP && !hasOptimization()){
		std::ostream output(getRes());
		printSatisfiable(output, modes().aspcomp3type);
		printSatisfiable(clog, modes().aspcomp3type, modes().verbosity);
	}

	printSolveEnd(verbosity());

	return sat;
}

//Translate into original vocabulary
vector<Literal> WLSImpl::getBackMappedModel(const vec<Lit>& model) const{
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); j++){
		if(!getRemapper()->wasInput(var(model[j]))){ //drop all literals that were not part of the input
			continue;
		}
		outmodel.push_back(getRemapper()->getLiteral(model[j]));
	}
	sort(outmodel.begin(), outmodel.end());
	return outmodel;
}

void WLSImpl::addModel(const vec<Lit>& model, Solution* sol){
	//Translate into original vocabulary
	vector<Literal> outmodel(getBackMappedModel(model));

	//Add to solution
	assert(sol!=NULL);
	sol->addModel(outmodel);

	//Print if requested
	if(sol->getPrint()){
		std::ostream output(getRes());

		if(sol->getNbModelsFound()==1){
			if(modes().aspcomp3type==ASPCOMP3_NOCOMP && !hasOptimization()){
				printSatisfiable(output, modes().aspcomp3type);
				printSatisfiable(clog, modes().aspcomp3type, modes().verbosity);
			}
			getTranslator().printHeader(output);
		}
		if(!hasOptimization()){
			printNbModels(clog, sol->getNbModelsFound(), verbosity());
		}
		getTranslator().printModel(output, outmodel);
	}
}

void WLSImpl::modelWasOptimal(){
	assert(hasOptimization());
	std::ostream output(getRes());
	printOptimalModelFound(output, modes().aspcomp3type);
}

///////
// PROP SOLVER PIMPL
///////

WPCLSImpl::WPCLSImpl(const SolverOption& modes)
		:WLSImpl(modes), solver(new PCSolver(modes, this)){
}

WPCLSImpl::~WPCLSImpl(){
	delete solver;
}

void WPCLSImpl::addVar(Atom v){
	Var newv = checkAtom(v);
	getSolver()->addVar(newv);
}

bool WPCLSImpl::addClause(vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(ll);
}

bool WPCLSImpl::addEquivalence(const Literal& head, const vector<Literal>& body, bool conj){
	Lit h = checkLit(head);
	vec<Lit> b;
	checkLits(body, b);
	return getSolver()->addEquivalence(h, b, conj);
}

bool WPCLSImpl::addRule(bool conj, Literal head, const vector<Literal>& lits){
	Lit newhead = checkLit(head);
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(conj, newhead, ll);
}

bool WPCLSImpl::addRuleToID(int defid, bool conj, Literal head, const vector<Literal>& lits){
	Lit newhead = checkLit(head);
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRuleToID(defid, conj, newhead, ll);
}

bool WPCLSImpl::addSet(int id, const vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll);
}

//Might be implemented more efficiently in the future
bool WPCLSImpl::addSet(int id, const vector<WLtuple>& lws){
	vector<Literal> lits;
	vector<Weight> weights;

	for(vector<WLtuple>::const_iterator i=lws.begin(); i<lws.end(); i++){
		lits.push_back((*i).l);
		weights.push_back((*i).w);
	}

	return addSet(id, lits, weights);
}

bool WPCLSImpl::addSet(int id, const vector<Literal>& lits, const vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(id, ll, w);
}

bool WPCLSImpl::addAggrExpr(Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(checkLit(head), setid, bound, sign, type, sem);
}

bool WPCLSImpl::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	vec<Lit> ll;
	checkLits(lits, ll);
	setOptimization(true);
	return getSolver()->addMinimize(ll, subsetmnmz);
}

bool WPCLSImpl::addMinimize(const Atom head, const int setid, AggType type){
	setOptimization(true);
    return getSolver()->addMinimize(checkAtom(head), setid, type);
}

bool WPCLSImpl::addIntVar(int groundname, int min, int max){
	return getSolver()->addIntVar(groundname, min, max);
}

bool WPCLSImpl::addCPBinaryRel(Literal head, int groundname, EqType rel, int bound){
	return getSolver()->addCPBinaryRel(checkLit(head), groundname, rel, bound);
}

bool WPCLSImpl::addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2){
	return getSolver()->addCPBinaryRelVar(checkLit(head), groundname, rel, groundname2);
}

bool WPCLSImpl::addCPSum(Literal head, const vector<int>& termnames, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, bound);
}

bool WPCLSImpl::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int bound){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, bound);
}

bool WPCLSImpl::addCPSumVar(Literal head, const vector<int>& termnames, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, rel, rhstermname);
}

bool WPCLSImpl::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int rhstermname){
	return getSolver()->addCPSum(checkLit(head), termnames, mult, rel, rhstermname);
}

bool WPCLSImpl::addCPCount(const vector<int>& termnames, int value, EqType rel, int rhstermname){
	return getSolver()->addCPCount(termnames, value, rel, rhstermname);
}

bool WPCLSImpl::addCPAlldifferent(const vector<int>& termnames){
	return getSolver()->addCPAlldifferent(termnames);
}

///////
// MODEL SOLVER
///////

WSOLSImpl::WSOLSImpl(const SolverOption& modes):
		WLSImpl(modes), solver(new SOSolver(modes, this)){
}

WSOLSImpl::~WSOLSImpl(){
	delete solver;
}

void WSOLSImpl::addVar(vsize modid, Atom v){
	getSolver()->addVar(modid, checkAtom(v));
}

bool WSOLSImpl::addClause(vsize modid, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addClause(modid, ll);
}

bool WSOLSImpl::addRule(vsize modid, bool conj, Literal head, vector<Literal>& lits){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addRule(modid, conj, checkLit(head), ll);
}

bool WSOLSImpl::addSet(vsize modid, int id, vector<Literal>& lits, vector<Weight>& w){
	vec<Lit> ll;
	checkLits(lits, ll);
	return getSolver()->addSet(modid, id, ll, w);
}

//Might be implemented more efficiently in the future
bool WSOLSImpl::addSet(vsize modid, int id, vector<WLtuple>& lws){
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

bool WSOLSImpl::addAggrExpr(vsize modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getSolver()->addAggrExpr(modid, checkLit(head), setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool WSOLSImpl::addChild(vsize parent, vsize child, Literal head){
	return getSolver()->addChild(parent, child, checkLit(head));
}

bool WSOLSImpl::addAtoms(vsize modid, const vector<Atom>& atoms){
	vector<Var> aa;
	checkAtoms(atoms, aa);
	return getSolver()->addAtoms(modid, aa);
}
