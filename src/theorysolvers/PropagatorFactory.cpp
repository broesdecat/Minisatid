/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "theorysolvers/PropagatorFactory.hpp"

#include "theorysolvers/PCSolver.hpp"

#include <iostream>

#include "wrapper/InterfaceImpl.hpp"

#include "satsolver/SATSolver.hpp"
#include "modules/IDSolver.hpp"
#include "modules/AggSolver.hpp"
#include "modules/ModSolver.hpp"
#include "modules/LazyGrounder.hpp"
#include "modules/Symmetrymodule.hpp"

#ifdef CPSUPPORT
#include "modules/CPSolver.hpp"
#endif

#include "utils/Print.hpp"

#include "monitors/ECNFGraphPrinter.hpp"
#include "monitors/HumanReadableParsingPrinter.hpp"

using namespace std;
using namespace MinisatID;
using namespace Minisat;

PropagatorFactory::PropagatorFactory(const SolverOption& modes, PCSolver* engine) :
		engine(engine),
		parsing(true),
		satsolver(NULL),
		aggsolver(NULL), modsolver(NULL),
		symmsolver(NULL)
#ifdef CPSUPPORT
		,cpsolver(NULL)
#endif
		{
	satsolver = getEnginep()->getSATSolver();
#ifdef CPSUPPORT
	cpsolver = getEnginep()->getCPSolverp();
#endif

	//TODO create aggpropfactory and call finishparsing on it

	if(modes.printcnfgraph){
		parsingmonitors.push_back(new ECNFGraphPrinter(cout));
	}

	if(modes.verbosity>2){
		parsingmonitors.push_back(new HumanReadableParsingPrinter(clog));
	}

	for(vector<ParsingMonitor*>::const_iterator i = parsingmonitors.begin(); i<parsingmonitors.end(); ++i){
		(*i)->notifyStart();
	}
}

PropagatorFactory::~PropagatorFactory() {
	deleteList<ParsingMonitor>(parsingmonitors);
}

template<typename T>
void PropagatorFactory::notifyMonitorsOfAdding(const T& obj) const{
	for(vector<ParsingMonitor*>::const_iterator i = parsingmonitors.begin(); i<parsingmonitors.end(); ++i){
		(*i)->notifyadded(obj);
	}
}

void PropagatorFactory::setModSolver(ModSolver* m) {
	assert(isParsing());
	modsolver = m;
}

bool PropagatorFactory::hasIDSolver(defID id) const { return idsolvers.find(id)!=idsolvers.end(); }

IDSolver* PropagatorFactory::getIDSolver(defID id) {
	if(!hasIDSolver(id)){
		addIDSolver(id);
	}
	return idsolvers.at(id);
}

AggSolver* PropagatorFactory::getAggSolver() {
	if(!hasAggSolver()){
		addAggSolver();
	}
	return aggsolver;
}

void PropagatorFactory::addAggSolver(){
	assert(isParsing());
	aggsolver = new AggSolver(getEnginep());
	getEngine().accept(aggsolver, EXITCLEANLY);
}

void PropagatorFactory::addIDSolver(defID id){
	assert(isParsing());
	IDSolver* idsolver = new IDSolver(getEnginep(), id);
	getEngine().accept(idsolver, EXITCLEANLY);
	idsolvers.insert(pair<defID, IDSolver*>(id, idsolver));
}

void PropagatorFactory::addSymmSolver(){
	assert(isParsing());
	symmsolver = new SymmetryPropagator<PCSolver*>(getEnginep());
}
bool PropagatorFactory::hasSymmSolver() const {
	return symmsolver!=NULL;
}
SymmetryPropagator<PCSolver*>* PropagatorFactory::getSymmSolver() const {
	assert(hasSymmSolver());
	return symmsolver;
}

bool PropagatorFactory::add(const Var& v) {
	getEngine().createVar(v);
	return true;
}

void PropagatorFactory::addVars(const vec<Lit>& a) {
	for (int i = 0; i < a.size(); ++i) {
		add(var(a[i]));
	}
}

void PropagatorFactory::addVars(const vector<Lit>& a) {
	for (vector<Lit>::const_iterator i=a.begin(); i < a.end(); ++i) {
		add(var(*i));
	}
}

bool PropagatorFactory::add(const InnerDisjunction& formula){
	notifyMonitorsOfAdding(formula);

	addVars(formula.literals);

//	if(formula.literals.size()<3){
		return getSolver()->addClause(formula.literals);
/*	}else{
		LazyGrounder* g = new LazyGrounder(getEnginep());
		etEngine().accept(g, EXITCLEANLY);
		g->setClause(formula);
		return g;
	}*/
}

bool PropagatorFactory::add(const InnerEquivalence& formula){
	addVar(formula.head);
	addVars(formula.literals);
	bool notunsat = true;

	//create the completion
	vec<Lit> comp;
	comp.push(formula.head);

	for (int i = 0; i < formula.literals.size(); ++i) {
		comp.push(formula.literals[i]);
	}

	if (formula.conjunctive) {
		for (int i = 1; i < comp.size(); ++i) {
			comp[i] = ~comp[i];
		}
	} else {
		comp[0] = ~comp[0];
	}

	InnerDisjunction clause;
	comp.copyTo(clause.literals);
	notunsat = add(clause);

	for (int i = 1; notunsat && i < comp.size(); ++i) {
		InnerDisjunction binclause;
		binclause.literals.push(~comp[0]);
		binclause.literals.push(~comp[i]);
		notunsat = add(binclause);
	}

	return notunsat;
}

bool PropagatorFactory::add(const InnerRule& formula){
	notifyMonitorsOfAdding(formula);

	add(formula.head);
	addVars(formula.body);
	return getIDSolver(formula.definitionID)->addRule(formula.conjunctive, mkLit(formula.head, false), formula.body);
}

bool PropagatorFactory::add(const InnerWSet& formula){
	notifyMonitorsOfAdding(formula);

	addVars(formula.literals);
	return getAggSolver()->addSet(formula.setID, formula.literals, formula.weights);
}

bool PropagatorFactory::add(const InnerAggregate& formula){
	notifyMonitorsOfAdding(formula);

	if(!hasAggSolver()){
		stringstream ss;
		ss <<"The set with id " <<formula.setID <<" should be defined before any aggregates using it.\n";
		throw idpexception(ss.str());
	}

	return getAggSolver()->addAggrExpr(formula);
}

bool PropagatorFactory::add(const InnerReifAggregate& formula){
	notifyMonitorsOfAdding(formula);

	if(!hasAggSolver()){
		stringstream ss;
		ss <<"The set with id " <<formula.setID <<" should be defined before the aggregate with head " <<formula.head <<"\n";
		throw idpexception(ss.str());
	}

	add(formula.head);
	if(formula.sem == DEF){
		return getAggSolver()->addDefinedAggrExpr(formula, getIDSolver(formula.defID));
	}else{
		return getAggSolver()->addAggrExpr(formula);
	}
}

bool PropagatorFactory::add(const InnerMinimizeSubset& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	addVars(formula.literals);
	getEngine().addOptimization(SUBSETMNMZ, formula.literals);
	return true;
}

bool PropagatorFactory::add(const InnerMinimizeOrderedList& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	addVars(formula.literals);
	getEngine().addOptimization(MNMZ, formula.literals);

	return true;
}
bool PropagatorFactory::add(const InnerMinimizeAgg& formula){
	notifyMonitorsOfAdding(formula);

	add(formula.head);
	getEngine().addOptimization(AGGMNMZ, formula.head);
	InnerDisjunction clause;
	clause.literals.push(mkLit(formula.head, false));
	bool notunsat = add(clause);
	if (notunsat) {
		assert(getAggSolver()!=NULL);
		notunsat = getAggSolver()->addMnmz(formula.head, formula.setID, formula.type);
	}
	return notunsat;
}

bool PropagatorFactory::add(const InnerForcedChoices& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.forcedchoices.size() != 0) {
		getSolver()->addForcedChoices(formula.forcedchoices);
	}
	return true;
}

bool PropagatorFactory::add(const InnerSymmetryLiterals& formula){
	notifyMonitorsOfAdding(formula);

	getSymmSolver()->add(formula.literalgroups);
	return true;
}

bool PropagatorFactory::add(const InnerSymmetry& formula){
	notifyMonitorsOfAdding(formula);

	getSymmSolver()->add(formula.symmetry);
	return true;
}

template<class T>
bool PropagatorFactory::addCP(const T& formula){
	notifyMonitorsOfAdding(formula);
#ifndef CPSUPPORT
	assert(false);
	exit(1);
#else
	return getCPSolver()->add(formula);
#endif
}

#ifdef CPSUPPORT
#warning Counting models in the presence of CP variables will be an underapproximation! (finding only one variable assigment for each literal assignment)

CPSolver* PropagatorFactory::getCPSolver() {
	assert(cpsolver!=NULL);
	return cpsolver;
}
#endif

bool PropagatorFactory::add(const InnerIntVarRange& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerIntVarEnum& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPBinaryRel& obj){
	add(obj.head);
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPBinaryRelVar& obj){
	add(obj.head);
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPSumWeighted& obj){
	add(obj.head);
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPCount& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPAllDiff& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(InnerDisjunction& formula, rClause& newclause){
	notifyMonitorsOfAdding(formula);
	addVars(formula.literals);

	return getSolver()->addClause(formula.literals, newclause);
}

void PropagatorFactory::finishParsing() {
	assert(isParsing());
	parsing = false;

	for(vector<ParsingMonitor*>::const_iterator i = parsingmonitors.begin(); i<parsingmonitors.end(); ++i){
		(*i)->notifyEnd();
	}
}
