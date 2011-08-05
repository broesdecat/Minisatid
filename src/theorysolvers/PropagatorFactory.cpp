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
#include "modules/aggsolver/Agg2SAT.hpp"
#include "modules/IDSolver.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/ModSolver.hpp"
#include "modules/LazyGrounder.hpp"
#include "modules/Symmetrymodule.hpp"
#include "modules/BinConstr.hpp"

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
		modsolver(NULL),
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

int PropagatorFactory::newSetID(){
	assert(!isParsing());
	return maxset++;
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

bool PropagatorFactory::add(const InnerSet& formula){
	InnerWSet set;
	set.setID = formula.setID;
	set.literals = formula.literals;
	set.weights.resize(set.literals.size(), 1);
	return add(set);
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
	}

	assert(formula.literals.size()>0 && formula.literals.size()==formula.weights.size());

	vector<WL> lw;
	for (vsize i = 0; i < formula.literals.size(); ++i) {
#ifdef NOARBITPREC
		if(formula.weights[i] == posInfinity() || formula.weights[i] == negInfinity()){
			throw idpexception(
				"Weights equal to or larger than the largest integer number "
				"are not allowed in limited precision.\n");
		}
#endif
		lw.push_back(WL(formula.literals[i], formula.weights[i]));
	}

	TypedSet* set = new TypedSet(getEnginep(), formula.setID);
	set->setWL(lw);

	if(isParsing()){
		parsedsets.insert(pair<int, TypedSet*>(formula.setID, set));
	}

	// FIXME initialize immediately if no longer parsing

	return true;
}

bool PropagatorFactory::add(const InnerAggregate& formula){
	notifyMonitorsOfAdding(formula);

	if(parsedsets.find(formula.setID)==parsedsets.end()){
		stringstream ss;
		ss <<"The set with id " <<formula.setID <<" should be defined before any aggregates using it.\n";
		throw idpexception(ss.str());
	}

	if(isParsing()){
		parsedaggs.push_back(new InnerAggregate(formula));
		return true;
	}

	InnerReifAggregate r = InnerReifAggregate();
	r.bound = formula.bound;
	r.defID = -1;
	r.head = dummyvar;
	r.sem = COMP;
	r.setID = formula.setID;
	r.sign	= formula.sign;
	r.type	= formula.type;
	return add(r);
}

bool PropagatorFactory::addAggrExpr(const InnerReifAggregate& agg){
	if(parsedsets.find(agg.setID)==parsedsets.end()){
		throwUndefinedSet(agg.setID);
	}

	if(agg.sem==DEF){
		TypedSet* set = parsedsets.at(agg.setID);
		InnerWSet innerset;
		innerset.setID = agg.setID;
		for(auto i=set->getWL().begin(); i!=set->getWL().end(); ++i){
			innerset.literals.push_back((*i).getLit());
			innerset.weights.push_back((*i).getWeight());
		}
		getIDSolver(agg.defID)->addDefinedAggregate(agg, innerset);
	}
	AggBound b(agg.sign, agg.bound);
	return addAggrExpr(agg.head, agg.setID, b, agg.type, agg.sem);
}

bool PropagatorFactory::addAggrExpr(Var headv, int setid, const AggBound& bound, AggType type, AggSem sem){
	assert(isParsing());

	TypedSet* set = parsedsets.at(setid);

	// Check whether the head occurs in the body of the set, which is not allowed
	for (vsize i = 0; i < set->getWL().size(); ++i) {
		if (var(set->getWL()[i].getLit()) == headv) { //Exception if head occurs in set itself
			char s[100];
			sprintf(s, "Set nr. %d contains a literal of atom %d, the head of an aggregate, which is not allowed.\n", setid, getPrintableVar(headv));
			throw idpexception(s);
		}
	}

#ifdef DEBUG
	if(type == CARD) { //Check if all card weights are 1
		for(vwl::size_type i=0; i<set->getWL().size(); ++i) {
			if(set->getWL()[i].getWeight()!=1) {
				report("Cardinality was loaded with wrong weights");
				assert(false);
			}
		}
	}
#endif

	getEngine().varBumpActivity(headv); // NOTE heuristic! (TODO move)

	//the head of the aggregate
	Lit head = mkLit(headv, false);

	Agg* agg = new Agg(head, AggBound(bound),sem==DEF?COMP:sem, type);
	set->addAgg(agg);

	if (getEngine().verbosity() >= 2) { //Print info on added aggregate
		MinisatID::print(getEngine().verbosity(), *agg);
		report("\n");
	}

	return true;
}

bool PropagatorFactory::add(const InnerReifAggregate& agg){
	notifyMonitorsOfAdding(agg);

	if(parsedsets.find(agg.setID)==parsedsets.end()){
		stringstream ss;
		ss <<"The set with id " <<agg.setID <<" should be defined before the aggregate with head " <<agg.head <<"\n";
		throw idpexception(ss.str());
	}

	add(agg.head);

	return addAggrExpr(agg);
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
bool PropagatorFactory::add(const InnerMinimizeVar& formula){
	notifyMonitorsOfAdding(formula);

	// FIXME check var existence and add optim intvar to pcsolver
	return true;
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

int IntVar::maxid_ = 0;

bool PropagatorFactory::add(const InnerIntVarRange& obj){
	if(intvars.find(obj.varID)==intvars.end()){
		// todo throw exception
	}
	intvars.insert(pair<int, IntVar*>(obj.varID, new IntVar(getEnginep(), obj.varID, obj.minvalue, obj.maxvalue)));
	return true;
}

bool PropagatorFactory::add(const InnerIntVarEnum& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPBinaryRel& obj){
	//TODO new BinaryConstraint(getEnginep(), intvars.at(obj.varID), obj.bound, obj.head);
	return true;
}

bool PropagatorFactory::add(const InnerCPBinaryRelVar& obj){
	add(obj.head);
	new BinaryConstraint(getEnginep(), intvars.at(obj.lhsvarID), obj.rel, intvars.at(obj.rhsvarID), obj.head);
	return true;
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

	bool notunsat = true;

	// aggregate checking
	dummyvar = getEngine().newVar();
	InnerDisjunction clause;
	clause.literals.push(mkLit(dummyvar));
	add(clause);
	for(auto i=parsedaggs.begin(); notunsat && i!=parsedaggs.end(); ++i){
		InnerReifAggregate r;
		r.bound = (*i)->bound;
		r.defID = -1;
		r.head = dummyvar;
		r.sem = COMP;
		r.setID = (*i)->setID;
		r.sign	= (*i)->sign;
		r.type	= (*i)->type;
		notunsat = add(r);
	}
	deleteList<InnerAggregate>(parsedaggs);

	// FIXME initialize aggregate sets via finishparsing!

	// FIXME we miss newly created sets here, add to addaggrexpr also!
	if(getEngine().modes().pbsolver){
		transformSumsToCNF(getEngine(), parsedsets);
	}

	// rule adding
	for(auto i=parsedrules.begin(); notunsat && i!=parsedrules.end(); ++i){
		notunsat = getIDSolver((*i)->definitionID)->addRule((*i)->conjunctive, (*i)->head, (*i)->body);
	}
	parsedrules.clear();

	if(not notunsat){
		//FIXME
	}
}

void PropagatorFactory::includeCPModel(std::vector<VariableEqValue>& varassignments){
	for(auto i=intvars.begin(); i!=intvars.end(); ++i){
		VariableEqValue vareq;
		vareq.variable = (*i).first;
		vareq.value = (*i).second->minValue();
		varassignments.push_back(vareq);
	}
}
