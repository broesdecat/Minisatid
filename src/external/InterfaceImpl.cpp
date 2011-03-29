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
#include "external/MonitorInterface.hpp"

using namespace std;
using namespace MinisatID;
using namespace MinisatID::Print;

// REMAPPER

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
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); ++i){
		ll.push(checkLit(*i));
	}
}

void WLSImpl::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	ll.reserve(lits.size());
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); ++i){
		ll.push_back(checkLit(*i));
	}
}

void WLSImpl::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll){
	ll.reserve(atoms.size());
	for(vector<Atom>::const_iterator i=atoms.begin(); i<atoms.end(); ++i){
		ll.push_back(checkAtom(*i));
	}
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
		getTranslator().printModel(output, outmodel);
	}
	if(!hasOptimization()){
		printNbModels(clog, getNbModelsFound(), verbosity());
	}
}

void WLSImpl::notifyOptimalModelFound(){
	assert(hasOptimization());
	getSolution().notifyOptimalModelFound();
}

//Translate into original vocabulary
bool WLSImpl::canBackMapLiteral(const Lit& lit) const{
	return getRemapper()->wasInput(var(lit));
}
Literal WLSImpl::getBackMappedLiteral(const Lit& lit) const{
	assert(!getRemapper()->wasInput(var(lit)));
	return getRemapper()->getLiteral(lit);
}

vector<Literal> WLSImpl::getBackMappedModel(const vec<Lit>& model) const{
	vector<Literal> outmodel;
	for(int i=0; i<model.size(); ++i){
		if(canBackMapLiteral(model[i])){
			outmodel.push_back(getBackMappedLiteral(model[i]));
		}
	}
	sort(outmodel.begin(), outmodel.end());
	return outmodel;
}

void WLSImpl::addMonitor(Monitor * const mon){
	monitors.push_back(mon);
	getSolver()->notifyHasMonitor();
}

template<>
void WLSImpl::notifyMonitor(const InnerPropagation& obj){
	if(canBackMapLiteral(obj.propagation)){
		Literal lit = getBackMappedLiteral(obj.propagation);
		for(vector<Monitor*>::const_iterator i=monitors.begin(); i<monitors.end(); ++i){
			(*i)->notifyPropagated(lit, obj.decisionlevel);
		}
	}
}

template<>
void WLSImpl::notifyMonitor(const InnerBacktrack& obj){
	for(vector<Monitor*>::const_iterator i=monitors.begin(); i<monitors.end(); ++i){
		(*i)->notifyBacktracked(obj.untillevel);
	}
}


// PROP SOLVER PIMPL

WPCLSImpl::WPCLSImpl(const SolverOption& modes)
		:WLSImpl(modes), solver(new PCSolver(modes, *this)){
}

WPCLSImpl::~WPCLSImpl(){
	delete solver;
}

bool WPCLSImpl::add(const Atom& v){
	return getSolver()->add(checkAtom(v));
}

bool WPCLSImpl::add(const Disjunction& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(d);
}
bool WPCLSImpl::add(const DisjunctionRef& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(d);
}
bool WPCLSImpl::add(const Equivalence& sentence){
	InnerEquivalence eq;
	eq.head = checkLit(sentence.head);
	checkLits(sentence.literals, eq.literals);
	eq.conjunctive = sentence.conj;
	return getSolver()->add(eq);
}
bool WPCLSImpl::add(const Rule& sentence){
	InnerRule rule;
	rule.head = checkAtom(sentence.head);
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body);
	return getSolver()->add(rule);
}
bool WPCLSImpl::add(const Set& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights.resize(set.literals.size(), 1);
	return getSolver()->add(set);
}
bool WPCLSImpl::add(const WSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights = sentence.weights;
	return getSolver()->add(set);
}
bool WPCLSImpl::add(const WLSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	for(vector<WLtuple>::const_iterator i=sentence.wl.begin(); i<sentence.wl.end(); ++i){
		set.literals.push_back(checkLit((*i).l));
		set.weights.push_back((*i).w);
	}
	return getSolver()->add(set);
}
bool WPCLSImpl::add(const Aggregate& sentence){
	InnerAggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head);
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	return getSolver()->add(agg);
}
bool WPCLSImpl::add(const MinimizeSubset& sentence){
	InnerMinimizeSubset mnm;
	checkLits(sentence.literals, mnm.literals);
	setOptimization(true);
	return getSolver()->add(mnm);
}
bool WPCLSImpl::add(const MinimizeOrderedList& sentence){
	InnerMinimizeOrderedList mnm;
	checkLits(sentence.literals, mnm.literals);
	setOptimization(true);
	return getSolver()->add(mnm);
}
bool WPCLSImpl::add(const MinimizeAgg& sentence){
	InnerMinimizeAgg mnm;
	mnm.head = checkAtom(sentence.head);
	mnm.setid = sentence.setid;
	mnm.type = sentence.type;
	setOptimization(true);
	return getSolver()->add(mnm);
}
bool WPCLSImpl::add(const ForcedChoices& sentence){
	InnerForcedChoices choices;
	checkLits(sentence.forcedchoices, choices.forcedchoices);
	return getSolver()->add(choices);
}

/*
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
}*/

// MODAL SOLVER

WSOLSImpl::WSOLSImpl(const SolverOption& modes):
		WLSImpl(modes), solver(new SOSolver(modes, *this)){
}

WSOLSImpl::~WSOLSImpl(){
	delete solver;
}

bool WSOLSImpl::add(int modid, const Atom& v){
	return getSolver()->add(modid, checkAtom(v));
}

bool WSOLSImpl::add(int modid, const Disjunction& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(modid, d);
}
bool WSOLSImpl::add(int modid, const DisjunctionRef& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(modid, d);
}
bool WSOLSImpl::add(int modid, const Rule& sentence){
	InnerRule rule;
	rule.head = checkAtom(sentence.head);
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body);
	return getSolver()->add(modid, rule);
}
bool WSOLSImpl::add(int modid, const Set& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights.resize(set.literals.size(), 1);
	return getSolver()->add(modid, set);
}
bool WSOLSImpl::add(int modid, const WSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights = sentence.weights;
	return getSolver()->add(modid, set);
}
bool WSOLSImpl::add(int modid, const WLSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	for(vector<WLtuple>::const_iterator i=sentence.wl.begin(); i<sentence.wl.end(); ++i){
		set.literals.push_back(checkLit((*i).l));
		set.weights.push_back((*i).w);
	}
	return getSolver()->add(modid, set);
}
bool WSOLSImpl::add(int modid, const Aggregate& sentence){
	InnerAggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head);
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	return getSolver()->add(modid, agg);
}

bool WSOLSImpl::add(int modalid, const RigidAtoms& sentence){
	InnerRigidAtoms rigid;
	checkAtoms(sentence.rigidatoms, rigid.rigidatoms);
	return getSolver()->add(modalid, rigid);
}
bool WSOLSImpl::add(int modalid, const SubTheory& sentence){
	InnerSubTheory subtheory;
	subtheory.child = sentence.child;
	subtheory.head = checkLit(sentence.head);
	return getSolver()->add(modalid, subtheory);
}
