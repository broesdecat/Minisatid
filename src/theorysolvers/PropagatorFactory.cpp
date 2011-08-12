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
#include "modules/aggsolver/AggTransform.hpp"
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
	for(auto i=parsedsets.begin(); i!=parsedsets.end(); ++i){
		delete((*i).second.first);
	}
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

bool PropagatorFactory::add(const InnerWLSet& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.wls.size() == 0) {
		throwEmptySet(formula.setID);
	}

	for(auto i=formula.wls.begin(); i!=formula.wls.end(); ++i){
		addVar((*i).getLit());
	}

	if(formula.setID>maxset){
		maxset = formula.setID;
	}

	if (contains(parsedsets, formula.setID)) {
		throwDoubleDefinedSet(formula.setID);
	}

	assert(formula.wls.size()>0);

	// TODO only if type is known here verifySet(formula);

	parsedsets.insert(pair<int, SetWithAggs>(formula.setID, SetWithAggs(new InnerWLSet(formula), vector<Agg*>())));

	return true;
}

bool PropagatorFactory::add(const InnerAggregate& agg){
	notifyMonitorsOfAdding(agg);

	if(parsedsets.find(agg.setID)==parsedsets.end()){
		throwUndefinedSet(agg.setID);
	}

	if(isParsing()){
		parsedaggs.push_back(new InnerAggregate(agg));
		return true;
	}else{
		InnerReifAggregate r = InnerReifAggregate();
		r.bound = agg.bound;
		r.defID = -1;
		r.head = dummyvar;
		r.sem = COMP;
		r.setID = agg.setID;
		r.sign	= agg.sign;
		r.type	= agg.type;
		return add(r);
	}
}

bool PropagatorFactory::add(const InnerReifAggregate& origagg){
	notifyMonitorsOfAdding(origagg);
	InnerReifAggregate newagg(origagg);

	if(parsedsets.find(newagg.setID)==parsedsets.end()){
		throwUndefinedSet(newagg.setID);
	}

	add(newagg.head);

	auto setwithagg = parsedsets.at(newagg.setID);
	if(newagg.type == MIN){
		newagg.type = MAX;
		newagg.sign = newagg.sign==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
		newagg.bound = -newagg.bound;
		if(setwithagg.second.size()==0){ // FIXME ugly: check whether it is the first MIN agg added to the set
			InnerWLSet* set = setwithagg.first;
			vector<WL> newwls;
			for(auto i=set->getWL().begin(); i!=set->getWL().end(); ++i){
				newwls.push_back(WL((*i).getLit(), -(*i).getWeight()));
			}
			set->wls = newwls;
		}
	}
	if(newagg.sem==DEF){
		getIDSolver(newagg.defID)->addDefinedAggregate(newagg, *setwithagg.first);
	}
	return addAggrExpr(newagg.head, newagg.setID, newagg.sign, newagg.bound, newagg.type, newagg.sem);
}

bool PropagatorFactory::addAggrExpr(Var head, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem){
	assert(type!=MIN);
	SetWithAggs& set = parsedsets.at(setid);

	if(set.second.size()==0){ // FIXME add this to the parser and remove it from here
		set.first->type = type;
	}

	verifyAggregate(set.first, head, type);

	getEngine().varBumpActivity(head); // NOTE heuristic! (TODO move)

	Agg* agg = new Agg(mkPosLit(head), AggBound(sign, bound),sem==DEF?COMP:sem, type);
	set.second.push_back(agg);

	if(not isParsing()){
		finishSet(set.first, set.second);
		/*FIXME assert(getEngine().getCurrentDecisionLevel()==0);
		if(getEngine().modes().pbsolver){
			map<int, TypedSet*> newsets;
			newsets[setid] = set;
			transformSumsToCNF(getEngine(), newsets);
		}

		bool present = false, unsat = false;
		set->finishParsing(present, unsat);
		if(unsat){
			throw idpexception("Adding unsatisfiable aggregates during search is not handled correctly at the moment.\n");
		}
		if(not present){
			delete(set);
			parsedsets.erase(setid); // TODO might still be present in event datastructures => should be removed by those in fact!
		}*/
	}

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
bool PropagatorFactory::add(const InnerMinimizeVar& formula){
	notifyMonitorsOfAdding(formula);

#warning MinimizeVar is not handled at the moment
	// TODO check var existence and add optim intvar to pcsolver
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

	if(!hasSymmSolver()){
		addSymmSolver();
	}

	getSymmSolver()->add(formula.literalgroups);
	return true;
}

bool PropagatorFactory::add(const InnerSymmetry& formula){
	notifyMonitorsOfAdding(formula);

	if(!hasSymmSolver()){
		addSymmSolver();
	}

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

IntVar*	PropagatorFactory::getIntVar(int varID) const {
	if(intvars.find(varID)==intvars.end()){
		throw idpexception("Integer variable was not declared before use.\n");
	}
	return intvars.at(varID);
}

bool PropagatorFactory::add(const InnerIntVarRange& obj){
	if(intvars.find(obj.varID)!=intvars.end()){
		stringstream ss;
		ss <<"Integer variable " <<obj.varID <<" was declared twice.\n";
		throw idpexception(ss.str());
	}
	intvars.insert(pair<int, IntVar*>(obj.varID, new IntVar(getEnginep(), obj.varID, obj.minvalue, obj.maxvalue)));
	return true;
}

bool PropagatorFactory::add(const InnerIntVarEnum& obj){
	return addCP(obj);
}

bool PropagatorFactory::add(const InnerCPBinaryRel& obj){
	InnerEquivalence eq;
	add(obj.head);
	eq.head = mkPosLit(obj.head);
	IntVar* left = getIntVar(obj.varID);
	switch(obj.rel){
		case MEQ:
			eq.literals.push(left->getEQLit(obj.bound));
			break;
		case MNEQ:
			eq.literals.push(left->getNEQLit(obj.bound));
			break;
		case MGEQ:
			eq.literals.push(left->getGEQLit(obj.bound));
			break;
		case MG:
			eq.literals.push(left->getGEQLit(obj.bound+1));
			break;
		case MLEQ:
			eq.literals.push(left->getLEQLit(obj.bound));
			break;
		case ML:
			eq.literals.push(left->getLEQLit(obj.bound-1));
			break;
	}
	return add(eq);
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

bool PropagatorFactory::finishSet(InnerWLSet* set, vector<Agg*>& aggs){
	bool unsat = false, sat = false;

	// transform into SAT if requested
	if(getEngine().modes().tocnf){
		if(!transformSumsToCNF(getEngine(), set, aggs)){
			return false;
		}
	}

	AggProp const * type = NULL;
	switch (set->type) {
		case MAX:
			type = AggProp::getMax(); break;
		case SUM:
			type = AggProp::getSum(); break;
		case CARD:
			type = AggProp::getCard(); break;
		case PROD:
			type = AggProp::getProd(); break;
		default: assert(false); break;
	}

	Weight knownbound;
	if(!sat && ! unsat){ setReduce(getEnginep(), set, aggs, *type, knownbound, unsat, sat); }
	if(!sat && ! unsat){ addHeadImplications(getEnginep(), set, aggs, unsat, sat); }
	if(!sat && ! unsat){ max2SAT(getEnginep(), set, aggs, unsat, sat); }
	if(!sat && ! unsat){ card2Equiv(getEnginep(), set, aggs, knownbound, unsat, sat); }
	if(!sat && ! unsat){
		decideUsingWatchesAndCreatePropagators(getEnginep(), set, aggs, knownbound);
	}
	aggs.clear();

	return !unsat;
}

bool PropagatorFactory::finishParsing() {
	assert(isParsing());
	parsing = false;

	for(auto i = parsingmonitors.begin(); i<parsingmonitors.end(); ++i){
		(*i)->notifyEnd();
	}

	bool notunsat = true;

	// create one, certainly true variable which can act as a dummy head
	dummyvar = getEngine().newVar();
	InnerDisjunction clause;
	clause.literals.push(mkLit(dummyvar));
	add(clause);

	// create reified aggregates
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

	for(auto i=parsedsets.begin(); notunsat && i!=parsedsets.end(); ++i){
		notunsat &= finishSet((*i).second.first, (*i).second.second);
	}

	// rule adding
	for(auto i=parsedrules.begin(); notunsat && i!=parsedrules.end(); ++i){
		notunsat &= getIDSolver((*i)->definitionID)->addRule((*i)->conjunctive, (*i)->head, (*i)->body);
	}
	deleteList<InnerRule>(parsedrules);

	return notunsat;
}

void PropagatorFactory::includeCPModel(std::vector<VariableEqValue>& varassignments){
	for(auto i=intvars.begin(); i!=intvars.end(); ++i){
		VariableEqValue vareq;
		vareq.variable = (*i).first;
		vareq.value = (*i).second->minValue();
		varassignments.push_back(vareq);
	}
}
