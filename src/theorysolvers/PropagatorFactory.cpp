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

void throwUndefinedSet(int setid){
	stringstream ss;
	ss <<"Set nr. " <<setid <<" is used, but not defined yet.\n";
	throw idpexception(ss.str());
}

void throwDoubleDefinedSet(int setid){
	stringstream ss;
	ss <<"Set nr. " <<setid <<" is defined more than once.\n";
	throw idpexception(ss.str());
}

void throwEmptySet(int setid){
	stringstream ss;
	ss <<"Set nr. " <<setid <<" is empty.\n";
	throw idpexception(ss.str());
}

void throwNegativeHead(Var head){
	stringstream ss;
	ss <<"An aggregate cannot be defined by a negative head, violated for " <<getPrintableVar(head) <<".\n";
	throw idpexception(ss.str());
}

void throwHeadOccursInSet(Var head, int setid){
	stringstream ss;
	ss <<"For the aggregated with head " <<getPrintableVar(head) <<" also occurs in its set.\n";
	throw idpexception(ss.str());
}

PropagatorFactory::PropagatorFactory(const SolverOption& modes, PCSolver* engine) :
		engine(engine),
		parsing(true),
		satsolver(NULL),
		aggsolver(NULL), modsolver(NULL),
		symmsolver(NULL)
#ifdef CPSUPPORT
		,cpsolver(NULL)
#endif
		,maxset(1)
		{
	satsolver = getEnginep()->getSATSolver();
	satsolver->notifyUsedForSearch();
#ifdef CPSUPPORT
	cpsolver = getEnginep()->getCPSolverp();
	cpsolver->notifyUsedForSearch();
#endif

	//TODO create aggpropfactory and call finishparsing on it

	if(modes.printcnfgraph){
		parsingmonitors.push_back(new ECNFGraphPrinter(cout));
	}

	if(modes.verbosity>2){
		parsingmonitors.push_back(new HumanReadableParsingPrinter(clog));
	}

	for(auto i = parsingmonitors.begin(); i<parsingmonitors.end(); ++i){
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
	aggsolver = new AggSolver(getEnginep());
	getEngine().accept(aggsolver, EV_EXITCLEANLY);
}

void PropagatorFactory::addIDSolver(defID id){
	IDSolver* idsolver = new IDSolver(getEnginep(), id);
	getEngine().accept(idsolver, EV_EXITCLEANLY);
	idsolvers.insert(pair<defID, IDSolver*>(id, idsolver));
}

void PropagatorFactory::addSymmSolver(){
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
	for (auto i=a.begin(); i!=a.end(); ++i) {
		add(var(*i));
	}
}

bool PropagatorFactory::add(const InnerDisjunction& formula){
	notifyMonitorsOfAdding(formula);

	addVars(formula.literals);

	// TODO lazygrounder
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

	parsedrules.push_back(new InnerRule(formula));
	return true;
}

bool PropagatorFactory::add(const InnerWSet& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.literals.size() == 0) {
		throwEmptySet(formula.setID);
	}

	addVars(formula.literals);

	if(formula.setID>maxset){
		maxset = formula.setID;
	}

	if (contains(parsedsets, formula.setID)) {
		throwDoubleDefinedSet(formula.setID);
	}else{
		parsedsets.insert(pair<int, InnerWSet*>(formula.setID, new InnerWSet(formula)));
	}

	return true;
}

bool PropagatorFactory::add(const InnerAggregate& formula){
	notifyMonitorsOfAdding(formula);

	if(parsedsets.find(formula.setID)==parsedsets.end()){
		stringstream ss;
		ss <<"The set with id " <<formula.setID <<" should be defined before any aggregates using it.\n";
		throw idpexception(ss.str());
	}

	parsedaggs.push_back(new InnerAggregate(formula));
	return true;
}

bool PropagatorFactory::add(const InnerReifAggregate& formula){
	notifyMonitorsOfAdding(formula);

	if(parsedsets.find(formula.setID)==parsedsets.end()){
		stringstream ss;
		ss <<"The set with id " <<formula.setID <<" should be defined before the aggregate with head " <<formula.head <<"\n";
		throw idpexception(ss.str());
	}

	add(formula.head);

	parsedreifaggs.push_back(new InnerReifAggregate(formula));
	return true;
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

	// aggregate checking
	Var v = getEngine().newVar();
	InnerDisjunction clause;
	clause.literals.push(mkLit(v));
	add(clause);
	for(auto i=parsedaggs.begin(); i!=parsedaggs.end(); ++i){
		InnerReifAggregate* r = new InnerReifAggregate();
		r->bound = (*i)->bound;
		r->defID = -1;
		r->head = v;
		r->sem = COMP;
		r->setID = (*i)->setID;
		r->sign	= (*i)->sign;
		r->type	= (*i)->type;
		parsedreifaggs.push_back(r);
	}
	deleteList<InnerAggregate>(parsedaggs);
	for(auto i=parsedreifaggs.begin(); i!=parsedreifaggs.end(); ++i){
		if(parsedsets.find((*i)->setID)==parsedsets.end()){
			throwUndefinedSet((*i)->setID);
		}
	}
	for(auto i=parsedreifaggs.begin(); i!=parsedreifaggs.end(); ++i){
		InnerWSet* set = parsedsets.at((*i)->setID);
		for(auto j=set->literals.begin(); j!=set->literals.end(); ++j){
			if (var(*j) == (*i)->head) {
				throwHeadOccursInSet((*i)->head, (*i)->setID);
			}
		}
		if((*i)->type==MIN){ // FIXME move somewhere else + code duplication with aggtransform
			//Transform Min into Max set: invert all weights
			auto newset = new InnerWSet(*set);
			newset->setID = ++maxset;
			(*i)->setID = newset->setID;
			parsedsets.insert(pair<int, InnerWSet*>(newset->setID, newset));
			newset->weights.clear();
			for (auto j=set->weights.begin(); j!=set->weights.end(); ++j) {
				newset->weights.push_back(-(*j));
			}

			//Invert the bound
			(*i)->bound = -(*i)->bound;
			(*i)->type = MAX;
			(*i)->sign = (*i)->sign==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
		}
	}
#ifdef DEBUG
	for(auto i=parsedreifaggs.begin(); i!=parsedreifaggs.end(); ++i){
		if((*i)->type==CARD){
			InnerWSet* set = parsedsets.at((*i)->setID);
			for(auto j=set->weights.begin(); j!=set->weights.end(); ++j){
				assert(*j==1);
			}
		}
	}
#endif

	bool notunsat = true;
	// aggregate adding
	for(auto i=parsedsets.begin(); i!=parsedsets.end(); ++i){
		getAggSolver()->addSet((*i).second->setID, (*i).second->literals, (*i).second->weights);
	}
	for(auto i=parsedreifaggs.begin(); notunsat && i!=parsedreifaggs.end(); ++i){
		if((*i)->sem==DEF){
			getIDSolver((*i)->defID)->addDefinedAggregate(**i, *parsedsets.at((*i)->setID));
		}
		notunsat = getAggSolver()->addAggrExpr(**i);
	}
	deleteList<InnerReifAggregate>(parsedreifaggs);
	deleteList<InnerWSet>(parsedsets);

	// rule adding
	for(auto i=parsedrules.begin(); notunsat && i!=parsedrules.end(); ++i){
		notunsat = getIDSolver((*i)->definitionID)->addRule((*i)->conjunctive, (*i)->head, (*i)->body);
	}
	parsedrules.clear();

	if(not notunsat){
		//FIXME
	}
}
