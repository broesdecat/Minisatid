/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
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

// PIMPL of External Interfaces

WLSImpl::WLSImpl(const SolverOption& modes):
		optimization(false),
		printedbestmodel(false),
		state(INIT), _modes(modes),
		remapper(modes.remap?new SmartRemapper():new Remapper()),
		owntranslator(new Translator()),
		translator(owntranslator) //Default translator is alwasy loaded
		{
}

WLSImpl::~WLSImpl(){
	if(owntranslator!=NULL){
		delete owntranslator;
	}
	delete remapper;
}

void WLSImpl::setTranslator(Translator* trans){
	translator = trans;
}

Translator& WLSImpl::getTranslator() {
	return *translator;
}

void WLSImpl::printStatistics() const {
	printStartStatistics();
	getSolver()->printStatistics();
}

void WLSImpl::printLiteral(std::ostream& output, const Lit& l) const{
	getTranslator().printLiteral(output, getRemapper()->getLiteral(l));
}

void WLSImpl::printCurrentOptimum(const Weight& value) const{
	ostream output(getRes());
	getTranslator().printCurrentOptimum(output, value);
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
	ll.reserve(lits.size());
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); i++){
		ll.push_back(checkLit(*i));
	}
}

void WLSImpl::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll){
	ll.reserve(atoms.size());
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
	double cpu_time = cpuTime();
	printInitDataStart(verbosity());

	bool present = true, unsat = false;
	getSolver()->finishParsing(present, unsat);
	state = PARSED;

	printInitDataEnd(verbosity(), cpuTime()-cpu_time, unsat);

	return !unsat;
}

bool WLSImpl::simplify(){
	double cpu_time = cpuTime();
	printSimpStart(verbosity());
	bool unsat = !getSolver()->simplify();
	state = SIMPLIFIED;

	printSimpEnd(verbosity(), cpuTime()-cpu_time, unsat);

	return !unsat;
}

/*
 * Solution options:
 * 		PRINT_NONE: never print any models
 * 		PRINT_BEST: after solving an optimization problem, only print the optimum model or the best model when notifyTimeout is called
 * 			when not an optimization problem, comes down to print all
 * 		PRINT_ALL: print every model when adding it to the solution
 *
 * 		MODELEXAND: search for a solution
 * 		PROPAGATE: only do unit propagation (and print nothing, not even when a model is found)
 */
bool WLSImpl::solve(Solution* sol){
	bool unsat = false;
	setSolution(sol);

	if(!unsat && state==INIT){
		unsat = !finishParsing();
	}
	if(!unsat && state==PARSED){
		unsat = !simplify();
	}

	if(!unsat){
		assert(state==SIMPLIFIED);

		double cpu_time = cpuTime();
		printSolveStart(verbosity());

		vec<Lit> assumptions;
		checkLits(getSolution().getAssumptions(), assumptions);

		unsat = !getSolver()->solve(assumptions, getSolution().getOptions());

		if(getSolution().getInferenceOption()==MODELEXPAND){
			state = SOLVED;
			if(hasOptimization() && getSolution().getPrintOption()==PRINT_BEST && !unsat){
				assert(getNbModelsFound()>0);

				std::ostream output(getRes());
				if(getSolution().hasOptimalModel()){
					printOptimalModelFound(output, modes().format);
				}
				getTranslator().printModel(output, getSolution().getBestModelFound());
				printedbestmodel = true;
			}
		}

		printSolveEnd(verbosity(), cpuTime()-cpu_time);
	}

	if(unsat){
		std::ostream output(getRes());
		printUnSatisfiable(output, modes().format, modes().transformat);
		printUnSatisfiable(clog, modes().format, modes().transformat, modes().verbosity);
	}else{
		if(!hasOptimization() && modes().transformat==TRANS_ASP){
			std::ostream output(getRes());
			printSatisfiable(output, modes().format, modes().transformat);
			printSatisfiable(clog, modes().format, modes().transformat, modes().verbosity);
		}
	}

	setSolution(NULL);

	return !unsat;
}

void WLSImpl::notifyTimeout(){
	//if optimization and best model has not been printed, print it now
	if(hasOptimization() && getSolution().getPrintOption()==PRINT_BEST && getSolution().getNbModelsFound()>0 && !printedbestmodel){
		ostream output(getRes());
		if(getSolution().hasOptimalModel()){
			printOptimalModelFound(output, modes().format);
		}
		getTranslator().printModel(output, getSolution().getBestModelFound());
		printedbestmodel = true;
	}
}

void WLSImpl::addModel(const vec<Lit>& model){
	vector<Literal> outmodel(getBackMappedModel(model));

	getSolution().addModel(outmodel, hasOptimization());

	if(getSolution().getPrintOption()==PRINT_ALL || (!hasOptimization() && getSolution().getPrintOption()==PRINT_BEST)){
		std::ostream output(getRes());
		if(getNbModelsFound()==1){
			if(!hasOptimization() && modes().transformat!=TRANS_ASP){
				printSatisfiable(output, modes().format, modes().transformat);
				printSatisfiable(clog, modes().format, modes().transformat, modes().verbosity);
			}
			getTranslator().printHeader(output);
		}
		if(!hasOptimization()){
			printNbModels(clog, getNbModelsFound(), verbosity());
		}
		getTranslator().printModel(output, outmodel);
	}
}

void WLSImpl::notifyOptimalModelFound(){
	assert(hasOptimization());
	getSolution().notifyOptimalModelFound();
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

// PROP SOLVER PIMPL

WPCLSImpl::WPCLSImpl(const SolverOption& modes)
		:WLSImpl(modes), solver(new PCSolver(modes, *this)){
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
	lits.reserve(lws.size());
	vector<Weight> weights;
	weights.reserve(lws.size());

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

// MODAL SOLVER

WSOLSImpl::WSOLSImpl(const SolverOption& modes):
		WLSImpl(modes), solver(new SOSolver(modes, *this)){
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
	lits.reserve(lws.size());
	vector<Weight> weights;
	weights.reserve(lws.size());

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
