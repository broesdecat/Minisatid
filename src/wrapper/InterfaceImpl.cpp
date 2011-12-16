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
#include <algorithm>

#include "external/ResourceManager.hpp"
#include "utils/Print.hpp"
#include "external/Translator.hpp"
#include "external/SearchMonitor.hpp"

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

	auto i = origtocontiguousatommapper.find(atom.getValue());
	Var v = 0;
	if(i==origtocontiguousatommapper.cend()){
		origtocontiguousatommapper.insert(pair<int, int>(atom.getValue(), maxnumber));
		contiguoustoorigatommapper.insert(pair<int, int>(maxnumber, atom.getValue()));
		v = maxnumber++;
	}else{
		v = (*i).second;
	}
	return v;
}

Var SmartRemapper::getNewVar(){
	return maxnumber++; // FIXME check invariants on the data structures!
}

bool SmartRemapper::wasInput(Var var) const{
	return contiguoustoorigatommapper.find(var)!=contiguoustoorigatommapper.cend();
}

Literal SmartRemapper::getLiteral(const Lit& lit){
	atommap::const_iterator atom = contiguoustoorigatommapper.find(var(lit));
	assert(atom!=contiguoustoorigatommapper.cend());
	int origatom = (*atom).second;
	return Literal(origatom, sign(lit));
}

bool SmartRemapper::hasVar(const Atom& atom, Var& mappedvarifexists) const{
	atommap::const_iterator i = origtocontiguousatommapper.find(atom.getValue());
	if(i==origtocontiguousatommapper.cend()){
		return false;
	}else{
		mappedvarifexists = (*i).second;
		return true;
	}
}

// PIMPL of External Interfaces


// Create var in the remapper which has original value, but which can be used safely by the solver.
Var WrapperPimpl::getNewVar(){
	return getRemapper()->getNewVar();
}

WrapperPimpl::WrapperPimpl(const SolverOption& modes):
		optimization(false),
		state(INIT),
		_modes(modes),

		// FIXME needed for being able to introduce new variables as soon as possible
		remapper(/*modes.remap?*/new SmartRemapper()/*:new Remapper()*/),
		sharedremapper(false),
		solutionmonitor(NULL)
		{
}
WrapperPimpl::WrapperPimpl(const SolverOption& modes, Remapper* sharedremapper):
		optimization(false),
		state(INIT),
		_modes(modes),
		remapper(sharedremapper),
		sharedremapper(true),
		solutionmonitor(NULL)
		{
}

WrapperPimpl::~WrapperPimpl(){
	if(not sharedremapper){
		delete remapper;
	}
}

void WrapperPimpl::setSolutionMonitor(Solution* sol) {
	if(sol!=NULL) {
		solutionmonitor = sol;
		getSolMonitor().setModes(modes());

		// FIXME check if this happens at the correct moment
		// NOTE: after parsing the translation, set the decision heuristic for the tseitins
		if(not modes().decideontseitins){
			dontDecideTseitins();
		}
	}
}

void WrapperPimpl::printStatistics() const {
	if(hasSolMonitor()){
		getSolMonitor().printStatistics();
	}
	getSolver()->printStatistics();
}

void WrapperPimpl::printLiteral(std::ostream& output, const Lit& l) const{
	if(canBackMapLiteral(l)){
		getSolMonitor().printLiteral(output, getRemapper()->getLiteral(l));
	}
}

void WrapperPimpl::printCurrentOptimum(const Weight& value) const{
	getSolMonitor().notifyCurrentOptimum(value);
}

Var WrapperPimpl::checkAtom(const Atom& atom){
	return getRemapper()->getVar(atom);
}

Lit WrapperPimpl::checkLit(const Literal& lit){
	return mkLit(checkAtom(lit.getAtom()), lit.hasSign());
}

void WrapperPimpl::checkLits(const vector<vector<Literal> >& lits, vector<vector<Lit> >& ll){
	for(vector<vector<Literal> >::const_iterator i=lits.cbegin(); i<lits.cend(); ++i){
		ll.push_back(vector<Lit>());
		checkLits(*i, ll.back());
	}
}

void WrapperPimpl::checkLits(const vector<Literal>& lits, vector<Lit>& ll){
	ll.reserve(lits.size());
	for(vector<Literal>::const_iterator i=lits.cbegin(); i<lits.cend(); ++i){
		ll.push_back(checkLit(*i));
	}
}

void WrapperPimpl::checkAtoms(const vector<Atom>& atoms, vector<Var>& ll){
	ll.reserve(atoms.size());
	for(vector<Atom>::const_iterator i=atoms.cbegin(); i<atoms.cend(); ++i){
		ll.push_back(checkAtom(*i));
	}
}

void WrapperPimpl::checkAtoms(const std::map<Atom, Atom>& atoms, std::map<Var, Var>& ll){
	for(auto i=atoms.cbegin(); i!=atoms.cend(); ++i){
		ll.insert(pair<Var, Var>(checkAtom((*i).first), checkAtom((*i).second)));
	}
}

SATVAL WrapperPimpl::finishParsing(){
	if(hasSolMonitor()){
		getSolMonitor().notifyStartDataInit();
		printInitDataStart(verbosity());
	}

	bool unsat = false;
	getSolver()->finishParsing(unsat);
	if(unsat){
		if(hasSolMonitor()){
			getSolMonitor().notifyUnsat();
		}
	}
	state = PARSED;

	if(hasSolMonitor()){
		getSolMonitor().notifyEndDataInit();
		printInitDataEnd(verbosity(), getSolMonitor().isUnsat());
	}

	return unsat?SATVAL::UNSAT:SATVAL::POS_SAT;
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
		if(finishParsing()==SATVAL::UNSAT){
			getSolMonitor().notifyUnsat();
		}
	}

	if(!getSolMonitor().isUnsat()){
		assert(state==PARSED);

		getSolMonitor().notifyStartSolving();
		printSolveStart(verbosity());

		litlist assumptions;
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

void WrapperPimpl::printTheory(ostream& stream){
	if(state==INIT){
		finishParsing();
	}
	getSolver()->printTheory(stream);
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
vector<Literal> WrapperPimpl::getBackMappedModel(const std::vector<Lit>& model) const{
	vector<Literal> outmodel;
	for(auto i=model.cbegin(); i!=model.cend(); ++i){
		if(canBackMapLiteral(*i)){
			outmodel.push_back(getBackMappedLiteral(*i));
		}
	}
	sort(outmodel.begin(), outmodel.end());
	return outmodel;
}

void WrapperPimpl::addMonitor(SearchMonitor * const mon){
	monitors.push_back(mon);
	getSolver()->requestMonitor(this);
}

template<>
void WrapperPimpl::notifyMonitor(const InnerPropagation& obj){
	if(canBackMapLiteral(obj.propagation)){
		Literal lit = getBackMappedLiteral(obj.propagation);
		for(auto i=monitors.cbegin(); i<monitors.cend(); ++i){
			(*i)->notifyPropagated(lit, obj.decisionlevel);
		}
	}
}

template<>
void WrapperPimpl::notifyMonitor(const InnerBacktrack& obj){
	for(auto i=monitors.cbegin(); i<monitors.cend(); ++i){
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
SATVAL PCWrapperPimpl::add(const Atom& v){
	getSolver()->add(checkAtom(v));
	return SATVAL::POS_SAT;
}

template<>
SATVAL PCWrapperPimpl::add(const Disjunction& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	getSolver()->add(d);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const DisjunctionRef& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	getSolver()->add(d);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const Equivalence& sentence){
	InnerEquivalence eq;
	eq.head = checkLit(sentence.head);
	checkLits(sentence.body, eq.literals);
	eq.conjunctive = sentence.conjunctive;
	getSolver()->add(eq);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const Rule& sentence){
	InnerRule rule;
	rule.head = checkAtom(sentence.head);
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body);
	getSolver()->add(rule);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const Set& sentence){
	WSet set;
	set.setID = sentence.setID;
	set.literals = sentence.literals;
	set.weights = vector<Weight>(sentence.literals.size(), 1);
	add(set);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const WSet& sentence){
	WLSet set;
	set.setID = sentence.setID;
	for(uint i=0; i<sentence.literals.size(); ++i){
		set.wl.push_back(WLtuple(sentence.literals[i], sentence.weights[i]));
	}
	add(set);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const WLSet& sentence){
	vector<WL> wls;
	for(auto i=sentence.wl.cbegin(); i<sentence.wl.cend(); ++i){
		wls.push_back(WL(checkLit((*i).l), (*i).w));
	}
	InnerWLSet set(sentence.setID, wls);
	getSolver()->add(set);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const Aggregate& sentence){
	InnerReifAggregate agg;
	agg.setID = sentence.setID;
	agg.head = checkAtom(sentence.head);
	agg.bound = sentence.bound;
	agg.type = sentence.type;
	agg.sign = sentence.sign;
	agg.sem = sentence.sem;
	agg.defID = sentence.defID;
	getSolver()->add(agg);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const MinimizeSubset& sentence){
	InnerMinimizeSubset mnm;
	checkLits(sentence.literals, mnm.literals);
	getSolver()->add(mnm);

	setOptimization(true);

	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const MinimizeOrderedList& sentence){
	InnerMinimizeOrderedList mnm;
	checkLits(sentence.literals, mnm.literals);
	getSolver()->add(mnm);

	setOptimization(true);

	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const MinimizeVar& sentence){
	InnerMinimizeVar mnm;
	mnm.varID = sentence.varID;
	getSolver()->add(mnm);

	setOptimization(true);

	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const MinimizeAgg& sentence){
	InnerMinimizeAgg mnm;
	mnm.head = checkAtom(sentence.head);
	mnm.setID = sentence.setid;
	mnm.type = sentence.type;
	setOptimization(true);
	getSolver()->add(mnm);

	setOptimization(true);

	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const ForcedChoices& sentence){
	InnerForcedChoices choices;
	checkLits(sentence.forcedchoices, choices.forcedchoices);
	getSolver()->add(choices);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const SymmetryLiterals& sentence){
	InnerSymmetryLiterals symms;
	checkLits(sentence.symmgroups, symms.literalgroups);
	getSolver()->add(symms);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const Symmetry& sentence){
	InnerSymmetry symms;
	checkAtoms(sentence.symmetry, symms.symmetry);
	getSolver()->add(symms);
	return getSolver()->satState();
}

template<>
SATVAL PCWrapperPimpl::add(const LazyGroundLit& sentence){
	InnerLazyClause lc;
	lc.monitor = sentence.monitor;
	lc.residual = checkLit(sentence.residual);
	lc.watchboth = sentence.watchboth;
	getSolver()->add(lc);
	return getSolver()->satState();
}

void checkCPSupport(){
#ifndef CPSUPPORT
	throw idpexception(getNoCPSupportString());
#endif
}

template<>
SATVAL PCWrapperPimpl::add(const CPIntVarEnum& sentence){
	checkCPSupport();
	InnerIntVarEnum var;
	var.varID = sentence.varID;
	var.values = sentence.values;
	getSolver()->add(var);
	return getSolver()->satState();
}
template<>
SATVAL PCWrapperPimpl::add(const CPIntVarRange& sentence){
	InnerIntVarRange var;
	var.varID = sentence.varID;
	var.minvalue = sentence.minvalue;
	var.maxvalue = sentence.maxvalue;
	getSolver()->add(var);
	return getSolver()->satState();
}
template<>
SATVAL PCWrapperPimpl::add(const CPBinaryRel& sentence){
	checkCPSupport();
	InnerCPBinaryRel form;
	form.head = checkAtom(sentence.head);
	form.varID = sentence.varID;
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	getSolver()->add(form);
	return getSolver()->satState();
}
template<>
SATVAL PCWrapperPimpl::add(const CPBinaryRelVar& sentence){
	InnerCPBinaryRelVar form;
	form.head = checkAtom(sentence.head);
	form.lhsvarID = sentence.lhsvarID;
	form.rel = sentence.rel;
	form.rhsvarID = sentence.rhsvarID;
	getSolver()->add(form);
	return getSolver()->satState();
}
template<>
SATVAL PCWrapperPimpl::add(const CPSumWeighted& sentence){
	checkCPSupport();
	InnerCPSumWeighted form;
	form.head = checkAtom(sentence.head);
	form.rel = sentence.rel;
	form.bound = sentence.bound;
	form.weights = sentence.weights;
	form.varIDs = sentence.varIDs;
	getSolver()->add(form);
	return getSolver()->satState();
}
template<>
SATVAL PCWrapperPimpl::add(const CPCount& sentence){
	checkCPSupport();
	InnerCPCount form;
	form.varIDs = sentence.varIDs;
	form.eqbound = sentence.eqbound;
	form.rel = sentence.rel;
	form.rhsvar = sentence.rhsvar;
	getSolver()->add(form);
	return getSolver()->satState();
}
template<>
SATVAL PCWrapperPimpl::add(const CPAllDiff& sentence){
	checkCPSupport();
	InnerCPAllDiff form;
	form.varIDs = sentence.varIDs;
	getSolver()->add(form);
	return getSolver()->satState();
}

// MODAL SOLVER

SOWrapperPimpl::SOWrapperPimpl(const SolverOption& modes):
		WrapperPimpl(modes), solver(new SOSolver(modes, *this)){
}

SOWrapperPimpl::~SOWrapperPimpl(){
	delete solver;
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const Atom& v){
	return getSolver()->add(modid, checkAtom(v));
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const Disjunction& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(modid, d);
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const DisjunctionRef& sentence){
	InnerDisjunction d;
	checkLits(sentence.literals, d.literals);
	return getSolver()->add(modid, d);
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const Rule& sentence){
	InnerRule rule;
	rule.head = checkAtom(sentence.head);
	rule.definitionID = sentence.definitionID;
	rule.conjunctive = sentence.conjunctive;
	checkLits(sentence.body, rule.body);
	return getSolver()->add(modid, rule);
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const Set& sentence){
	vector<Weight> weights = vector<Weight>(sentence.literals.size(), 1);
	InnerWLSet set(sentence.setID, vector<WL>());
	for(auto i=sentence.literals.cbegin(); i!=sentence.literals.cend(); ++i){
		set.wls.push_back(WL(checkLit(*i), 1));
	}
	return getSolver()->add(modid, set);
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const WSet& sentence){
	InnerWLSet set(sentence.setID, vector<WL>());
	for(uint i=0; i!=sentence.literals.size(); ++i){
		set.wls.push_back(WL(checkLit(sentence.literals[i]), sentence.weights[i]));
	}
	return getSolver()->add(modid, set);
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const WLSet& sentence){
	InnerWLSet set(sentence.setID, vector<WL>());
	for(vector<WLtuple>::const_iterator i=sentence.wl.cbegin(); i<sentence.wl.cend(); ++i){
		set.wls.push_back(WL(checkLit((*i).l),(*i).w));
	}
	return getSolver()->add(modid, set);
}

template<>
SATVAL SOWrapperPimpl::add(int modid, const Aggregate& sentence){
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
SATVAL SOWrapperPimpl::add(int modalid, const RigidAtoms& sentence){
	InnerRigidAtoms rigid;
	checkAtoms(sentence.rigidatoms, rigid.rigidatoms);
	return getSolver()->add(modalid, rigid);
}

template<>
SATVAL SOWrapperPimpl::add(int modalid, const SubTheory& sentence){
	InnerSubTheory subtheory;
	subtheory.child = sentence.child;
	subtheory.head = checkLit(sentence.head);
	return getSolver()->add(modalid, subtheory);
}
