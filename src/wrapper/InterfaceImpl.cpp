/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "wrapper/InterfaceImpl.hpp"

#include <cstdlib>
#include <vector>
#include <tr1/memory>
#include <algorithm>

#include "external/ResourceManager.hpp"
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
		state(INIT),
		_modes(modes),
		remapper(modes.remap?new SmartRemapper():new Remapper())
		{
}

WLSImpl::~WLSImpl(){
	delete remapper;
}

void WLSImpl::setSolutionMonitor(Solution* sol) {
	if(sol!=NULL) {
		solutionmonitor = sol;
		getSolMonitor().setModes(modes());
	}
}

void WLSImpl::printStatistics() const {
	getSolMonitor().printStatistics();
	getSolver()->printStatistics();
}

void WLSImpl::printLiteral(std::ostream& output, const Lit& l) const{
	getSolMonitor().getTranslator()->printLiteral(output, getRemapper()->getLiteral(l));
}

void WLSImpl::printCurrentOptimum(const Weight& value) const{
	//FIXME move to solutionmonitor and remove getres!
	ostream output(getRes());
	getSolMonitor().getTranslator()->printCurrentOptimum(output, value);
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
	if(solutionmonitor==NULL){
		throw idpexception("Solving without instantiating any solution monitor.\n");
	}

	getSolMonitor().notifyStartDataInit();
	printInitDataStart(verbosity());

	bool present = true, unsat = false;
	//FIXME check what present is doing here
	getSolver()->finishParsing(present, unsat);
	if(unsat){
		getSolMonitor().notifyUnsat();
	}
	state = PARSED;

	getSolMonitor().notifyEndDataInit();
	printInitDataEnd(verbosity(), getSolMonitor().isUnsat());

	return !getSolMonitor().isUnsat();
}

bool WLSImpl::simplify(){
	if(solutionmonitor==NULL){
		throw idpexception("Solving without instantiating any solution monitor.\n");
	}

	getSolMonitor().notifyStartSimplifying();
	printSimpStart(verbosity());
	if(!getSolver()->simplify()){
		getSolMonitor().notifyUnsat();
	}
	state = SIMPLIFIED;

	getSolMonitor().notifyEndSimplifying();
	printSimpEnd(verbosity(), getSolMonitor().isUnsat());

	return !getSolMonitor().isUnsat();
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
void WLSImpl::solve(){
	if(solutionmonitor==NULL){
		throw idpexception("Solving without instantiating any solution monitor.\n");
	}

	if(!getSolMonitor().isUnsat() && state==INIT){
		if(!finishParsing()){
			getSolMonitor().notifyUnsat();
		}
	}
	if(!getSolMonitor().isUnsat() && state==PARSED){
		if(!simplify()){
			getSolMonitor().notifyUnsat();
		}
	}

	if(!getSolMonitor().isUnsat()){
		assert(state==SIMPLIFIED);

		getSolMonitor().notifyStartSolving();
		printSolveStart(verbosity());

		vec<Lit> assumptions;
		checkLits(getSolMonitor().getAssumptions(), assumptions);

		if(!getSolver()->solve(assumptions, getSolMonitor().getOptions())){
			getSolMonitor().notifyUnsat();
		}

		if(getSolMonitor().getInferenceOption()==MODELEXPAND){
			state = SOLVED;
		}

		getSolMonitor().notifyEndSolving();
	}

	getSolMonitor().notifySolvingFinished();
}

void WLSImpl::addModel(const vec<Lit>& model){
	vector<Literal> outmodel(getBackMappedModel(model));
	getSolMonitor().addModel(outmodel);
}

void WLSImpl::notifyOptimalModelFound(){
	assert(hasOptimization());
	getSolMonitor().notifyOptimalModelFound();
}

bool WLSImpl::canBackMapLiteral(const Lit& lit) const{
	return getRemapper()->wasInput(var(lit));
}

Literal WLSImpl::getBackMappedLiteral(const Lit& lit) const{
	assert(canBackMapLiteral(lit));
	return getRemapper()->getLiteral(lit);
}

//Translate into original vocabulary
vector<Literal> WLSImpl::getBackMappedModel(const vec<Lit>& model) const{
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); ++j){
		if(canBackMapLiteral(model[j])){
			outmodel.push_back(getBackMappedLiteral(model[j]));
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
