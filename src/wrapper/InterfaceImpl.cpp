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

bool Remapper::hasVar(const Atom& atom, Var& mappedvarifexists) const{
	if(atom.getValue()<=maxnumber){
		mappedvarifexists = atom.getValue();
		return true;
	}else{
		return false;
	}
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

bool SmartRemapper::hasVar(const Atom& atom, Var& mappedvarifexists) const{
	atommap::const_iterator i = origtocontiguousatommapper.find(atom.getValue());
	if(i==origtocontiguousatommapper.end()){
		return false;
	}else{
		mappedvarifexists = (*i).second;
		return true;
	}
}

// PIMPL of External Interfaces

WrapperPimpl::WrapperPimpl(const SolverOption& modes):
		optimization(false),
		state(INIT),
		_modes(modes),
		remapper(modes.remap?new SmartRemapper():new Remapper())
		{
}

WrapperPimpl::~WrapperPimpl(){
	delete remapper;
}

void WrapperPimpl::setSolutionMonitor(Solution* sol) {
	if(sol!=NULL) {
		solutionmonitor = sol;
		getSolMonitor().setModes(modes());
		if(sol->hasTseitinKnowledge() && !modes().tseitindecisions){
			notifySmallestTseitin(sol->smallestTseitinAtom());
		}
	}
}

void WrapperPimpl::printStatistics() const {
	getSolMonitor().printStatistics();
	getSolver()->printStatistics();
}

void WrapperPimpl::printLiteral(std::ostream& output, const Lit& l) const{
	getSolMonitor().printLiteral(output, getRemapper()->getLiteral(l));
}

void WrapperPimpl::printCurrentOptimum(const Weight& value) const{
	getSolMonitor().notifyCurrentOptimum(value);
}

void WrapperPimpl::notifySmallestTseitin(const Atom& tseitin){
	Atom posstseitin = tseitin;
	while(true){
		Var var = 0;
		if(getRemapper()->hasVar(posstseitin, var)){
			getSolver()->notifyNonDecisionVar(var);
		}else{
			break;
		}
		posstseitin = Atom(posstseitin.getValue()+1);
	}
}
Var WrapperPimpl::checkAtom(const Atom& atom){
	return getRemapper()->getVar(atom);
}

Lit WrapperPimpl::checkLit(const Literal& lit){
	return mkLit(checkAtom(lit.getAtom()), lit.hasSign());
}

void WrapperPimpl::checkLits(const vector<Literal>& lits, vec<Lit>& ll){
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); ++i){
		ll.push(checkLit(*i));
	}
}

void WrapperPimpl::checkLits(const vector<vector<Literal> >& lits, vec<vec<Lit> >& ll){
	for(vector<vector<Literal> >::const_iterator i=lits.begin(); i<lits.end(); ++i){
		ll.push();
		for(vector<Literal>::const_iterator j=(*i).begin(); j<(*i).end(); ++j){
			ll.last().push(checkLit(*j));
		}
	}
}

void WrapperPimpl::checkLits(const vector<vector<Literal> >& lits, vector<vector<Lit> >& ll){
	for(vector<vector<Literal> >::const_iterator i=lits.begin(); i<lits.end(); ++i){
		ll.push_back(vector<Lit>());
		checkLits(*i, ll.back());
	}
}

void WrapperPimpl::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	ll.reserve(lits.size());
	for(vector<Literal>::const_iterator i=lits.begin(); i<lits.end(); ++i){
		ll.push_back(checkLit(*i));
	}
}

void WrapperPimpl::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll){
	ll.reserve(atoms.size());
	for(vector<Atom>::const_iterator i=atoms.begin(); i<atoms.end(); ++i){
		ll.push_back(checkAtom(*i));
	}
}

void WrapperPimpl::checkAtoms(const std::map<Atom, Atom>& atoms, std::map<Var, Var>& ll){
	for(auto i=atoms.begin(); i!=atoms.end(); ++i){
		ll.insert(pair<Var, Var>(checkAtom((*i).first), checkAtom((*i).second)));
	}
}

bool WrapperPimpl::finishParsing(){
	if(solutionmonitor==NULL){
		throw idpexception("Solving without instantiating any solution monitor.\n");
	}

	getSolMonitor().notifyStartDataInit();
	printInitDataStart(verbosity());

	bool unsat = false;
	getSolver()->finishParsing(unsat);
	if(unsat){
		getSolMonitor().notifyUnsat();
	}
	state = PARSED;

	getSolMonitor().notifyEndDataInit();
	printInitDataEnd(verbosity(), getSolMonitor().isUnsat());

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
void WrapperPimpl::solve(){
	if(solutionmonitor==NULL){
		throw idpexception("Solving without instantiating any solution monitor.\n");
	}

	if(!getSolMonitor().isUnsat() && state==INIT){
		if(!finishParsing()){
			getSolMonitor().notifyUnsat();
		}
	}

	if(!getSolMonitor().isUnsat()){
		assert(state==PARSED);

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

void WrapperPimpl::addModel(const InnerModel& model){
	Model* outmodel = new Model();
	outmodel->literalinterpretations = getBackMappedModel(model.litassignments);
	outmodel->variableassignments = model.varassignments;
	getSolMonitor().addModel(outmodel);
}

void WrapperPimpl::notifyOptimalModelFound(){
	assert(hasOptimization());
	getSolMonitor().notifyOptimalModelFound();
}

bool WrapperPimpl::canBackMapLiteral(const Lit& lit) const{
	return getRemapper()->wasInput(var(lit));
}

Literal WrapperPimpl::getBackMappedLiteral(const Lit& lit) const{
	assert(canBackMapLiteral(lit));
	return getRemapper()->getLiteral(lit);
}

//Translate into original vocabulary
vector<Literal> WrapperPimpl::getBackMappedModel(const vec<Lit>& model) const{
	vector<Literal> outmodel;
	for(int j=0; j<model.size(); ++j){
		if(canBackMapLiteral(model[j])){
			outmodel.push_back(getBackMappedLiteral(model[j]));
		}
	}
	sort(outmodel.begin(), outmodel.end());
	return outmodel;
}

void WrapperPimpl::addMonitor(Monitor * const mon){
	monitors.push_back(mon);
	getSolver()->requestMonitor(this);
}

template<>
void WrapperPimpl::notifyMonitor(const InnerPropagation& obj){
	if(canBackMapLiteral(obj.propagation)){
		Literal lit = getBackMappedLiteral(obj.propagation);
		for(vector<Monitor*>::const_iterator i=monitors.begin(); i<monitors.end(); ++i){
			(*i)->notifyPropagated(lit, obj.decisionlevel);
		}
	}
}

template<>
void WrapperPimpl::notifyMonitor(const InnerBacktrack& obj){
	for(vector<Monitor*>::const_iterator i=monitors.begin(); i<monitors.end(); ++i){
		(*i)->notifyBacktracked(obj.untillevel);
	}
}


// PROP SOLVER PIMPL

PCWrapperPimpl::PCWrapperPimpl(const SolverOption& modes)
		:WrapperPimpl(modes), solver(new PCSolver(modes, *this, 1)){
}

PCWrapperPimpl::~PCWrapperPimpl(){
	delete solver;
}

template<>
bool PCWrapperPimpl::add(const Atom& v){
	return getSolver()->add(checkAtom(v));
}

template<>
bool PCWrapperPimpl::add(const Disjunction& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(d);
}

template<>
bool PCWrapperPimpl::add(const DisjunctionRef& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(d);
}

template<>
bool PCWrapperPimpl::add(const Equivalence& sentence){
	InnerEquivalence eq;
	eq.head = checkLit(sentence.head);
	checkLits(sentence.body, eq.literals);
	eq.conjunctive = sentence.conjunctive;
	return getSolver()->add(eq);
}

template<>
bool PCWrapperPimpl::add(const Rule& sentence){
	InnerRule rule;
	rule.head = checkAtom(sentence.head);
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body);
	return getSolver()->add(rule);
}

template<>
bool PCWrapperPimpl::add(const Set& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights.resize(set.literals.size(), 1);
	return getSolver()->add(set);
}

template<>
bool PCWrapperPimpl::add(const WSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights = sentence.weights;
	return getSolver()->add(set);
}

template<>
bool PCWrapperPimpl::add(const WLSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	for(vector<WLtuple>::const_iterator i=sentence.wl.begin(); i<sentence.wl.end(); ++i){
		set.literals.push_back(checkLit((*i).l));
		set.weights.push_back((*i).w);
	}
	return getSolver()->add(set);
}

template<>
bool PCWrapperPimpl::add(const Aggregate& sentence){
	InnerReifAggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head);
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	return getSolver()->add(agg);
}

template<>
bool PCWrapperPimpl::add(const MinimizeSubset& sentence){
	InnerMinimizeSubset mnm;
	checkLits(sentence.literals, mnm.literals);
	setOptimization(true);
	return getSolver()->add(mnm);
}

template<>
bool PCWrapperPimpl::add(const MinimizeOrderedList& sentence){
	InnerMinimizeOrderedList mnm;
	checkLits(sentence.literals, mnm.literals);
	setOptimization(true);
	return getSolver()->add(mnm);
}

template<>
bool PCWrapperPimpl::add(const MinimizeVar& sentence){
	InnerMinimizeVar mnm;
	mnm.varID = sentence.varID;
	setOptimization(true);
	return getSolver()->add(mnm);
}

template<>
bool PCWrapperPimpl::add(const ForcedChoices& sentence){
	InnerForcedChoices choices;
	checkLits(sentence.forcedchoices, choices.forcedchoices);
	return getSolver()->add(choices);
}

template<>
bool PCWrapperPimpl::add(const SymmetryLiterals& sentence){
	InnerSymmetryLiterals symms;
	checkLits(sentence.symmgroups, symms.literalgroups);
	return getSolver()->add(symms);
}

template<>
bool PCWrapperPimpl::add(const Symmetry& sentence){
	InnerSymmetry symms;
	checkAtoms(sentence.symmetry, symms.symmetry);
	return getSolver()->add(symms);
}

void checkCPSupport(){
#ifndef CPSUPPORT
	throw idpexception(getNoCPSupportString());
#endif
}

template<>
bool PCWrapperPimpl::add(const CPIntVarEnum& sentence){
	checkCPSupport();
	InnerIntVarEnum var;
	var.varID = sentence.varID;
	var.values = sentence.values;
	return getSolver()->add(var);
}
template<>
bool PCWrapperPimpl::add(const CPIntVarRange& sentence){
	InnerIntVarRange var;
	var.varID = sentence.varID;
	var.minvalue = sentence.minvalue;
	var.maxvalue = sentence.maxvalue;
	return getSolver()->add(var);
}
template<>
bool PCWrapperPimpl::add(const CPBinaryRel& sentence){
	checkCPSupport();
	InnerCPBinaryRel form;
	form.head = checkAtom(sentence.head);
	form.varID = sentence.varID;
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	return getSolver()->add(form);
}
template<>
bool PCWrapperPimpl::add(const CPBinaryRelVar& sentence){
	InnerCPBinaryRelVar form;
	form.head = checkAtom(sentence.head);
	form.lhsvarID = sentence.lhsvarID;
	form.rel = sentence.rel;
	form.rhsvarID = sentence.rhsvarID;
	return getSolver()->add(form);
}
template<>
bool PCWrapperPimpl::add(const CPSumWeighted& sentence){
	checkCPSupport();
	InnerCPSumWeighted form;
	form.head = checkAtom(sentence.head);
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	form.weights = sentence.weights;
	form.varIDs = sentence.varIDs;
	return getSolver()->add(form);
}
template<>
bool PCWrapperPimpl::add(const CPCount& sentence){
	checkCPSupport();
	InnerCPCount form;
	form.varIDs = sentence.varIDs;
	form.eqbound = sentence.eqbound;
	form.rel = sentence.rel;
	form.rhsvar = sentence.rhsvar;
	return getSolver()->add(form);
}
template<>
bool PCWrapperPimpl::add(const CPAllDiff& sentence){
	checkCPSupport();
	InnerCPAllDiff form;
	form.varIDs = sentence.varIDs;
	return getSolver()->add(form);
}

// MODAL SOLVER

SOWrapperPimpl::SOWrapperPimpl(const SolverOption& modes):
		WrapperPimpl(modes), solver(new SOSolver(modes, *this)){
}

SOWrapperPimpl::~SOWrapperPimpl(){
	delete solver;
}

template<>
bool SOWrapperPimpl::add(int modid, const Atom& v){
	return getSolver()->add(modid, checkAtom(v));
}

template<>
bool SOWrapperPimpl::add(int modid, const Disjunction& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(modid, d);
}

template<>
bool SOWrapperPimpl::add(int modid, const DisjunctionRef& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(modid, d);
}

template<>
bool SOWrapperPimpl::add(int modid, const Rule& sentence){
	InnerRule rule;
	rule.head = checkAtom(sentence.head);
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body);
	return getSolver()->add(modid, rule);
}

template<>
bool SOWrapperPimpl::add(int modid, const Set& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights.resize(set.literals.size(), 1);
	return getSolver()->add(modid, set);
}

template<>
bool SOWrapperPimpl::add(int modid, const WSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	checkLits(sentence.literals, set.literals);
	set.weights = sentence.weights;
	return getSolver()->add(modid, set);
}

template<>
bool SOWrapperPimpl::add(int modid, const WLSet& sentence){
	InnerWSet set;
	set.setID = sentence.setID;
	for(vector<WLtuple>::const_iterator i=sentence.wl.begin(); i<sentence.wl.end(); ++i){
		set.literals.push_back(checkLit((*i).l));
		set.weights.push_back((*i).w);
	}
	return getSolver()->add(modid, set);
}

template<>
bool SOWrapperPimpl::add(int modid, const Aggregate& sentence){
	InnerReifAggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head);
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	return getSolver()->add(modid, agg);
}

template<>
bool SOWrapperPimpl::add(int modalid, const RigidAtoms& sentence){
	InnerRigidAtoms rigid;
	checkAtoms(sentence.rigidatoms, rigid.rigidatoms);
	return getSolver()->add(modalid, rigid);
}

template<>
bool SOWrapperPimpl::add(int modalid, const SubTheory& sentence){
	InnerSubTheory subtheory;
	subtheory.child = sentence.child;
	subtheory.head = checkLit(sentence.head);
	return getSolver()->add(modalid, subtheory);
}
