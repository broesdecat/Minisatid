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
#include "modules/LazyGrounder.hpp"

#ifdef CPSUPPORT
#include "modules/CPSolver.hpp"
#endif

#include "utils/Print.hpp"

#include "parser/parsingmonitors/ECNFGraphPrinter.hpp"
#include "parser/parsingmonitors/HumanReadableParsingPrinter.hpp"

using namespace std;
using namespace MinisatID;

using Minisat::vec;

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
		maxset(1)
		{
	SATStorage::setStorage(engine->getSATSolver());
	SATStorage::getStorage()->notifyUsedForSearch();
#ifdef CPSUPPORT
	CPStorage::setStorage(engine->getCPSolverp());
	CPStorage::getStorage()->notifyUsedForSearch();
#endif

	if(modes.printcnfgraph){
		parsingmonitors.push_back(new ECNFGraphPrinter(cout));
	}

	if(modes.verbosity>2){
		parsingmonitors.push_back(new HumanReadableParsingPrinter(clog));
	}

	for(auto i = parsingmonitors.cbegin(); i<parsingmonitors.cend(); ++i){
		(*i)->notifyStart();
	}
}

PropagatorFactory::~PropagatorFactory() {
	deleteList<ParsingMonitor>(parsingmonitors);
	for(auto i=parsedsets.cbegin(); i!=parsedsets.cend(); ++i){
		delete((*i).second.first);
	}
}

template<typename T>
void PropagatorFactory::notifyMonitorsOfAdding(const T& obj) const{
	for(vector<ParsingMonitor*>::const_iterator i = parsingmonitors.cbegin(); i<parsingmonitors.cend(); ++i){
		(*i)->notifyadded(obj);
	}
}

void PropagatorFactory::setModSolver(ModSolver* m) {
	assert(isParsing());
	ModStorage::setStorage(m);
}

bool PropagatorFactory::hasIDSolver(defID id) const { return idsolvers.find(id)!=idsolvers.cend(); }

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

void PropagatorFactory::add(const Var& v, bool nondecision) {
	getEngine().createVar(v, nondecision);
}

void PropagatorFactory::addVars(const vector<Lit>& a) {
	for (auto i=a.cbegin(); i!=a.cend(); ++i) {
		add(var(*i));
	}
}

int PropagatorFactory::newSetID(){
	assert(!isParsing());
	return maxset++;
}

void toVec(const std::vector<Lit>& literals, vec<Lit>& lits){
	for(auto i=literals.cbegin(); i<literals.cend(); ++i){
		lits.push(*i);
	}
}

void PropagatorFactory::add(const InnerDisjunction& clause){
	notifyMonitorsOfAdding(clause);

	addVars(clause.literals);

	// TODO 1-watched scheme
//	if(formula.literals.size()<3){
		vec<Lit> lits;
		toVec(clause.literals, lits);
		SATStorage::getStorage()->addClause(lits);
/*	}else{
		LazyGrounder* g = new LazyGrounder(getEnginep());
		etEngine().accept(g, EXITCLEANLY);
		g->setClause(formula);
		return g;
	}*/
}

void PropagatorFactory::add(const InnerEquivalence& formula){
	// TODO equiv propagator (or at least, 1-watched scheme for the long clause)
	addVar(formula.head);
	addVars(formula.literals);

	//create the completion
	InnerDisjunction comp;
	litlist& lits = comp.literals;
	lits.push_back(formula.head);

	for (int i = 0; i < formula.literals.size(); ++i) {
		lits.push_back(formula.literals[i]);
	}

	if (formula.conjunctive) {
		for (int i = 1; i < lits.size(); ++i) {
			lits[i] = ~lits[i];
		}
	} else {
		lits[0] = ~lits[0];
	}

	add(comp);

	for (int i = 1; i < lits.size(); ++i) {
		InnerDisjunction binclause;
		binclause.literals.push_back(~lits[0]);
		binclause.literals.push_back(~lits[i]);
		add(binclause);
	}
}

void PropagatorFactory::add(const InnerRule& rule){
	notifyMonitorsOfAdding(rule);

	add(rule.head);
	addVars(rule.body);

//	if(getEngine().modes().lazy){
		// FIXME LazyStorage::getStorage()->add(new InnerRule(rule));
//	}else{
		getIDSolver(rule.definitionID)->addRule(rule.conjunctive, rule.head, rule.body);
//	}
}

void PropagatorFactory::add(const std::vector<InnerRule*>& definition){
	// FIXME Add all rules to new idsolver and finish it
}

void PropagatorFactory::add(const InnerWLSet& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.wls.size() == 0) {
		throwEmptySet(formula.setID);
	}

	for(auto i=formula.wls.cbegin(); i!=formula.wls.cend(); ++i){
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

	parsedsets.insert(pair<int, SetWithAggs>(formula.setID, SetWithAggs(new InnerWLSet(formula), vector<TempAgg*>())));
}

void PropagatorFactory::add(const InnerAggregate& agg){
	notifyMonitorsOfAdding(agg);

	if(parsedsets.find(agg.setID)==parsedsets.cend()){
		throwUndefinedSet(agg.setID);
	}

	if(isParsing()){
		parsedaggs.push_back(new InnerAggregate(agg));
	}else{
		InnerReifAggregate r = InnerReifAggregate();
		r.bound = agg.bound;
		r.defID = -1;
		r.head = dummyvar;
		r.sem = COMP;
		r.setID = agg.setID;
		r.sign	= agg.sign;
		r.type	= agg.type;
		add(r);
	}
}

void PropagatorFactory::add(const InnerReifAggregate& origagg){
	notifyMonitorsOfAdding(origagg);
	InnerReifAggregate newagg(origagg);

	if(parsedsets.find(newagg.setID)==parsedsets.cend()){
		throwUndefinedSet(newagg.setID);
	}

	add(newagg.head);

	auto setwithagg = parsedsets.at(newagg.setID);
	if(setwithagg.second.empty()){
		setwithagg.first->type = origagg.type;
	}
	if(newagg.type == MIN){
		newagg.type = MAX;
		newagg.sign = newagg.sign==AGGSIGN_LB?AGGSIGN_UB:AGGSIGN_LB;
		newagg.bound = -newagg.bound;
		if(setwithagg.second.size()==0){ // FIXME ugly: check whether it is the first MIN agg added to the set
			InnerWLSet* set = setwithagg.first;
			vector<WL> newwls;
			for(auto i=set->getWL().cbegin(); i!=set->getWL().cend(); ++i){
				newwls.push_back(WL((*i).getLit(), -(*i).getWeight()));
			}
			set->wls = newwls;
		}
	}
	if(newagg.sem==DEF){
		getIDSolver(newagg.defID)->addDefinedAggregate(newagg, *setwithagg.first);
	}
	addAggrExpr(newagg.head, newagg.setID, newagg.sign, newagg.bound, newagg.type, newagg.sem);
}

void PropagatorFactory::addAggrExpr(Var head, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem){
	assert(type!=MIN);
	SetWithAggs& set = parsedsets.at(setid);

	if(set.second.size()==0){ // FIXME add this to the parser and remove it from here
		set.first->type = type;
	}

	verifyAggregate(set.first, head, type);

	getEngine().varBumpActivity(head); // NOTE heuristic! (TODO move)

	TempAgg* agg = new TempAgg(mkPosLit(head), AggBound(sign, bound),sem==DEF?COMP:sem, type);
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
}

void PropagatorFactory::add(const InnerMinimizeSubset& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	addVars(formula.literals);
	getEngine().addOptimization(Optim::SUBSET, formula.literals);
}

void PropagatorFactory::add(const InnerMinimizeOrderedList& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	addVars(formula.literals);
	getEngine().addOptimization(Optim::LIST, formula.literals);
}
void PropagatorFactory::add(const InnerMinimizeAgg& formula){
	notifyMonitorsOfAdding(formula);

	add(formula.head);

	InnerDisjunction d;
	d.literals.push_back(mkPosLit(formula.head));
	add(d);

	auto it = parsedsets.find(formula.setID);
	if(it==parsedsets.cend()){
		throwUndefinedSet(formula.setID);
	}
	auto set = it->second.first;
	set->type = formula.type;

	tempagglist aggs;
	AggBound bound(AggSign::AGGSIGN_UB, Weight(0));
	// FIXME IMPLICATION IS USED INCORRECTLY (but could be used here!)
	aggs.push_back(new TempAgg(mkPosLit(formula.head), bound, AggSem::COMP, formula.type));
	finishSet(set, aggs, true);
}
void PropagatorFactory::add(const InnerMinimizeVar& formula){
	notifyMonitorsOfAdding(formula);

#warning MinimizeVar is not handled at the moment
	// TODO check var existence and add optim intvar to pcsolver
}

void PropagatorFactory::add(const InnerForcedChoices& formula){
	notifyMonitorsOfAdding(formula);

	if (formula.forcedchoices.size() != 0) {
		vec<Lit> lits;
		toVec(formula.forcedchoices, lits);
		SATStorage::getStorage()->addForcedChoices(lits);
	}
}

void PropagatorFactory::add(const InnerSymmetryLiterals& formula){
	notifyMonitorsOfAdding(formula);

	if(not SymmStorage::hasStorage()){
		SymmStorage::addStorage(getEnginep());
	}

	SymmStorage::getStorage()->add(formula.literalgroups);
}

void PropagatorFactory::add(const InnerSymmetry& formula){
	notifyMonitorsOfAdding(formula);

	if(not SymmStorage::hasStorage()){
		SymmStorage::addStorage(getEnginep());
	}

	SymmStorage::getStorage()->add(formula.symmetry);
}

template<class T>
void PropagatorFactory::addCP(const T& formula){
	notifyMonitorsOfAdding(formula);
#ifndef CPSUPPORT
	assert(false);
	exit(1);
#else
	CPStorage::getStorage()->add(formula);
#warning Counting models in the presence of CP variables will be an underapproximation! (finding only one variable assigment for each literal assignment)
#endif
}

int IntVar::maxid_ = 0;

IntVar*	PropagatorFactory::getIntVar(int varID) const {
	if(intvars.find(varID)==intvars.cend()){
		throw idpexception("Integer variable was not declared before use.\n");
	}
	return intvars.at(varID);
}

void PropagatorFactory::add(const InnerIntVarRange& obj){
	if(intvars.find(obj.varID)!=intvars.cend()){
		stringstream ss;
		ss <<"Integer variable " <<obj.varID <<" was declared twice.\n";
		throw idpexception(ss.str());
	}
	intvars.insert(pair<int, IntVar*>(obj.varID, new IntVar(getEnginep(), obj.varID, toInt(obj.minvalue), toInt(obj.maxvalue))));
}

void PropagatorFactory::add(const InnerIntVarEnum& obj){
	addCP(obj);
}

void PropagatorFactory::add(const InnerCPBinaryRel& obj){
	InnerEquivalence eq;
	add(obj.head);
	eq.head = mkPosLit(obj.head);
	IntVar* left = getIntVar(obj.varID);
	int intbound = toInt(obj.bound);
	switch(obj.rel){
		case MEQ:
			eq.literals.push_back(left->getEQLit(intbound));
			break;
		case MNEQ:
			eq.literals.push_back(left->getNEQLit(intbound));
			break;
		case MGEQ:
			eq.literals.push_back(left->getGEQLit(intbound));
			break;
		case MG:
			eq.literals.push_back(left->getGEQLit(intbound+1));
			break;
		case MLEQ:
			eq.literals.push_back(left->getLEQLit(intbound));
			break;
		case ML:
			eq.literals.push_back(left->getLEQLit(intbound-1));
			break;
	}
	add(eq);
}

void PropagatorFactory::add(const InnerCPBinaryRelVar& obj){
	add(obj.head);
	new BinaryConstraint(getEnginep(), intvars.at(obj.lhsvarID), obj.rel, intvars.at(obj.rhsvarID), obj.head);
}

void PropagatorFactory::add(const InnerCPSumWeighted& obj){
	add(obj.head);
	addCP(obj);
}

void PropagatorFactory::add(const InnerCPCount& obj){
	addCP(obj);
}

void PropagatorFactory::add(const InnerCPAllDiff& obj){
	addCP(obj);
}

void PropagatorFactory::add(InnerDisjunction& formula, rClause& newclause){
	notifyMonitorsOfAdding(formula);
	addVars(formula.literals);

	vec<Lit> lits;
	toVec(formula.literals, lits);
	SATStorage::getStorage()->addClause(lits, newclause);
}

SATVAL PropagatorFactory::finishSet(InnerWLSet* set, vector<TempAgg*>& aggs, bool optimagg){

	bool unsat = false, sat = false;

	// transform into SAT if requested
	if(getEngine().modes().tocnf && not optimagg){
		if(not AggStorage::hasStorage()){
			AggStorage::addStorage(getEnginep());
		}
		AggStorage::getStorage()->add(set, aggs);
	}
	if(aggs.size()==0){
		return SATVAL::POS_SAT;
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

	Weight knownbound(0);
	if(not optimagg){ // TODO can we do better for minimization over aggregates?
		if(!sat && ! unsat){ setReduce(getEnginep(), set, aggs, *type, knownbound, unsat, sat); }
		if(!sat && ! unsat){ addHeadImplications(getEnginep(), set, aggs, unsat, sat); }
		if(!sat && ! unsat){ max2SAT(getEnginep(), set, aggs, unsat, sat); }
		if(!sat && ! unsat){ card2Equiv(getEnginep(), set, aggs, knownbound, unsat, sat); }
		if(!sat && ! unsat){
			decideUsingWatchesAndCreatePropagators(getEnginep(), set, aggs, knownbound);
		}
	}else{
		if(!sat && ! unsat){
			assert(aggs.size()==1);
			decideUsingWatchesAndCreateOptimPropagator(getEnginep(), set, aggs[0], knownbound);
		}
	}

	aggs.clear();

	return unsat?SATVAL::UNSAT:SATVAL::POS_SAT;
}

SATVAL PropagatorFactory::finishParsing() {
	assert(isParsing());
	parsing = false;

	for(auto i = parsingmonitors.cbegin(); i<parsingmonitors.cend(); ++i){
		(*i)->notifyEnd();
	}

	// create one, certainly true variable which can act as a dummy head
	dummyvar = getEngine().newVar();
	InnerDisjunction clause;
	clause.literals.push_back(mkLit(dummyvar));
	add(clause);

	SATVAL satval = SATVAL::POS_SAT;

	// create reified aggregates
	for(auto i=parsedaggs.cbegin(); satval==SATVAL::POS_SAT && i!=parsedaggs.cend(); ++i){
		InnerReifAggregate r;
		r.bound = (*i)->bound;
		r.defID = -1;
		r.head = dummyvar;
		r.sem = COMP;
		r.setID = (*i)->setID;
		r.sign	= (*i)->sign;
		r.type	= (*i)->type;
		add(r);
		satval &= getEngine().satState();
	}
	deleteList<InnerAggregate>(parsedaggs);

	for(auto i=parsedsets.begin(); satval==SATVAL::POS_SAT && i!=parsedsets.end(); ++i){
		satval &= finishSet((*i).second.first, (*i).second.second);
	}
	if(AggStorage::hasStorage()){
		satval &= AggStorage::getStorage()->execute();
	}

	return satval;
}

void PropagatorFactory::includeCPModel(std::vector<VariableEqValue>& varassignments){
	for(auto i=intvars.cbegin(); i!=intvars.cend(); ++i){
		VariableEqValue vareq;
		vareq.variable = (*i).first;
		vareq.value = (*i).second->minValue();
		varassignments.push_back(vareq);
	}
}

void PropagatorFactory::add(const InnerLazyClause& object){
	assert(getEngine().modes().lazy);
	assert(not getEngine().isDecisionVar(var(object.residual)));
			// TODO in fact, want to check that it does not yet occur in the theory, this is easiest hack
	addVar(object.residual, true); // NOTE: by default, do not decide on residuals
	if(object.watchboth){
		new LazyResidualWatch(getEnginep(), ~object.residual, object.monitor);
	}
	new LazyResidualWatch(getEnginep(), object.residual, object.monitor);
}
