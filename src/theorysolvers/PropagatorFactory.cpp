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

#include "satsolver/SATSolver.hpp"
#include "modules/aggsolver/Agg2SAT.hpp"
#include "modules/IDSolver.hpp"
#include "modules/aggsolver/AggSet.hpp"
#include "modules/aggsolver/AggTransform.hpp"
#include "modules/LazyGrounder.hpp"
#include "modules/symmetry/Symmetry.hpp"
#include "modules/BinConstr.hpp"
#include "modules/LazyGrounder.hpp"

#ifdef CPSUPPORT
#include "modules/cpsolver/CPSolver.hpp"
#endif

#include "utils/Print.hpp"

#include "constraintvisitors/ECNFGraphPrinter.hpp"
#include "constraintvisitors/HumanReadableParsingPrinter.hpp"

using namespace std;
using namespace MinisatID;

using Minisat::vec;

void throwUndefinedSet(int setid) {
	stringstream ss;
	ss << "Set nr. " << setid << " is used, but not defined yet.\n";
	throw idpexception(ss.str());
}

void throwDoubleDefinedSet(int setid) {
	stringstream ss;
	ss << "Set nr. " << setid << " is defined more than once.\n";
	throw idpexception(ss.str());
}

void throwNegativeHead(const std::string& head) {
	stringstream ss;
	ss << "An aggregate cannot be defined by a negative head, violated for " <<head << ".\n";
	throw idpexception(ss.str());
}

void throwHeadOccursInSet(const std::string& head, int setid) {
	stringstream ss;
	ss << "For the aggregated with head " <<head << " also occurs in set " <<setid <<".\n";
	throw idpexception(ss.str());
}

PropagatorFactory::PropagatorFactory(const SolverOption& modes, PCSolver* engine) :
		engine(engine),
		definitions(new Definition(engine)),
		parsing(true),
		maxset(1) {
	SATStorage::setStorage(engine->getSATSolver());
#ifdef CPSUPPORT
	CPStorage::setStorage(engine->getCPSolverp());
#endif

	if (modes.verbosity > 2) {
		parsingmonitors.push_back(new HumanReadableParsingPrinter<ostream>(getEnginep(), clog));
	}

	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyStart();
	}
}

PropagatorFactory::~PropagatorFactory() {
	deleteList<ConstraintVisitor>(parsingmonitors);
	for (auto i = parsedsets.cbegin(); i != parsedsets.cend(); ++i) {
		MAssert((*i).second.set!=NULL);
		delete ((*i).second.set);
	}
}

template<typename T>
void PropagatorFactory::notifyMonitorsOfAdding(const T& obj) const {
	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->visit(obj);
	}
}

int PropagatorFactory::newSetID() {
	MAssert(!isParsing());
	return maxset++;
}

void toVec(const std::vector<Lit>& literals, vec<Lit>& lits) {
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		lits.push(*i);
	}
}

void PropagatorFactory::add(const Disjunction& clause) {
	notifyMonitorsOfAdding(clause);
	SATStorage::getStorage()->addClause(clause.literals);
}

// Precondition: already added vars!
void PropagatorFactory::addImplication(const Lit& head, const litlist& body, bool conjunction) {
	if (conjunction) {
		Disjunction d;
		d.literals.resize(2, not head);
		for (auto i = body.cbegin(); i < body.cend(); ++i) {
			d.literals[1] = *i;
			add(d);
		}
	} else {
		Disjunction d;
		d.literals.insert(d.literals.begin(), body.cbegin(), body.cend());
		d.literals.push_back(not head);
		add(d);
	}
}

// Precondition: already added vars!
void PropagatorFactory::addReverseImplication(const Lit& head, const litlist& body, bool conjunction) {
	litlist list;
	for (auto i = body.cbegin(); i < body.cend(); ++i) {
		list.push_back(not *i);
	}
	addImplication(not head, list, not conjunction);
}

void PropagatorFactory::add(const Implication& formula) {
	// TODO equiv propagator (or 1-watched scheme for the long clause)

	switch (formula.type) {
	case ImplicationType::EQUIVALENT:
		addImplication(formula.head, formula.body, formula.conjunction);
		addReverseImplication(formula.head, formula.body, formula.conjunction);
		break;
	case ImplicationType::IMPLIEDBY:
		addReverseImplication(formula.head, formula.body, formula.conjunction);
		break;
	case ImplicationType::IMPLIES:
		addImplication(formula.head, formula.body, formula.conjunction);
		break;
	}
}

void PropagatorFactory::add(const Rule& rule) {
	notifyMonitorsOfAdding(rule);

	definitions->addRule(rule.definitionID, rule.conjunctive, rule.head, rule.body);
}

void PropagatorFactory::add(const WLSet& formula) {
	notifyMonitorsOfAdding(formula);

	if (formula.setID > maxset) {
		maxset = formula.setID;
	}

	if (contains(parsedsets, formula.setID)) {
		throwDoubleDefinedSet(formula.setID);
	}

	// TODO only if type is known here verifySet(formula);

	SetWithAggs sa;
	sa.set = new WLSet(formula);
	parsedsets.insert( { formula.setID, sa });
}

void PropagatorFactory::add(const Aggregate& origagg) {
	notifyMonitorsOfAdding(origagg);

	guaranteeAtRootLevel(); // TODO currently only at root level, should change?

	Aggregate newagg(origagg);

	if (parsedsets.find(newagg.setID) == parsedsets.cend()) {
		throwUndefinedSet(newagg.setID);
	}

	auto setwithagg = parsedsets.at(newagg.setID);
	if (newagg.type == AggType::MIN) {
		newagg.type = AggType::MAX;
		newagg.sign = newagg.sign == AggSign::LB ? AggSign::UB : AggSign::LB;
		newagg.bound = -newagg.bound;
		if (setwithagg.aggs.size() == 0) { // FIXME ugly: check whether it is the first MIN agg added to the set
			auto set = setwithagg.set;
			vector<WL> newwls;
			for (auto i = set->getWL().cbegin(); i != set->getWL().cend(); ++i) {
				newwls.push_back(WL((*i).getLit(), -(*i).getWeight()));
			}
			set->wl = newwls;
		}
	}
	if (newagg.sem == AggSem::DEF) {
		definitions->addDefinedAggregate(newagg, *setwithagg.set);
	}
	addAggrExpr(newagg.head, newagg.setID, newagg.sign, newagg.bound, newagg.type, newagg.sem);
}

void PropagatorFactory::addAggrExpr(Var head, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem) {
	MAssert(type!=AggType::MIN);
	auto& set = parsedsets.at(setid);

	if(set.aggs.size()==0){
		set.type = type;
	}

	verifyAggregate(set.set, set.type, head, type);

	getEngine().varBumpActivity(head); // NOTE heuristic! (TODO move)

	auto agg = new TempAgg(mkPosLit(head), AggBound(sign, bound), sem == AggSem::DEF ? AggSem::COMP : sem, type);
	set.aggs.push_back(agg);

	if (not isParsing()) {
		finishSet(set.set, set.aggs);
	}
}

void PropagatorFactory::add(const MinimizeSubset& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	OptimStatement optim(formula.priority, Optim::SUBSET, formula.literals);
	getEngine().addOptimization(optim);
}

void PropagatorFactory::add(const MinimizeOrderedList& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	OptimStatement optim(formula.priority, Optim::LIST, formula.literals);
	getEngine().addOptimization(optim);
}
void PropagatorFactory::add(const MinimizeAgg& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	auto head = getEngine().newVar();

	Disjunction d;
	d.literals.push_back(mkPosLit(head));
	add(d);

	auto it = parsedsets.find(formula.setid);
	if (it == parsedsets.cend()) {
		throwUndefinedSet(formula.setid);
	}
	auto set = it->second.set;

	if(it->second.aggs.size()==0){
		it->second.type = formula.type;
	}

	tempagglist aggs;
	AggBound bound(AggSign::UB, Weight(0));
	// FIXME IMPLICATION IS USED INCORRECTLY (but could be used here!)
	aggs.push_back(new TempAgg(mkPosLit(head), bound, AggSem::COMP, formula.type));
	finishSet(set, aggs, true, formula.priority);
}

void PropagatorFactory::add(const MinimizeVar& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	auto it = intvars.find(formula.varID);
	if(it==intvars.cend()){
		stringstream ss;
		ss <<"The CP var " <<formula.varID <<" has not been declared yet, but is used in an optimization statement.";
		throw idpexception(ss.str());
	}
	OptimStatement optim(formula.priority, it->second);
	getEngine().addOptimization(optim);
}

void PropagatorFactory::add(const Symmetry& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	new SymmetryPropagator(getEnginep(), formula);
}

template<class T>
void PropagatorFactory::addCP(const T& formula) {
	notifyMonitorsOfAdding(formula);
	guaranteeAtRootLevel();
#ifndef CPSUPPORT
	throw idpexception("Adding a finite domain constraint while minisatid was compiled without CP support\n");
#else
	CPStorage::getStorage()->add(formula);
	clog <<"Counting models in the presence of CP variables will be an under-approximation! (finding only one variable assingment for each literal assignment).\n";
#endif
}

int IntVar::maxid_ = 0;

IntVar* PropagatorFactory::getIntVar(int varID) const {
	if (intvars.find(varID) == intvars.cend()) {
		throw idpexception("Integer variable was not declared before use.\n");
	}
	return intvars.at(varID);
}

void PropagatorFactory::add(const IntVarRange& obj) {
	addCP(obj);
	// TODO also add a cpviagecode option!
	/*if(intvars.find(obj.varID)!=intvars.cend()){
	 stringstream ss;
	 ss <<"Integer variable " <<obj.varID <<" was declared twice.\n";
	 throw idpexception(ss.str());
	 }
	 intvars.insert(pair<int, IntVar*>(obj.varID, new IntVar(getEnginep(), obj.varID, toInt(obj.minvalue), toInt(obj.maxvalue))));*/
}

void PropagatorFactory::add(const IntVarEnum& obj) {
	addCP(obj);
}

void PropagatorFactory::add(const CPBinaryRel& obj) {
	addCP(obj);

	/*Equivalence eq;
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
	 add(eq);*/
}

void PropagatorFactory::add(const CPBinaryRelVar& obj) {
	addCP(obj);
	//new BinaryConstraint(getEnginep(), intvars.at(obj.lhsvarID), obj.rel, intvars.at(obj.rhsvarID), obj.head);
}

void PropagatorFactory::add(const CPSumWeighted& obj) {
	addCP(obj);
}

void PropagatorFactory::add(const CPCount& obj) {
	addCP(obj);
}

void PropagatorFactory::add(const CPAllDiff& obj) {
	addCP(obj);
}

void PropagatorFactory::guaranteeAtRootLevel(){
	// FIXME use reverse trail instead!
	if(getEngine().getCurrentDecisionLevel()>0){
		getEngine().backtrackTo(0);
	}
}

#define SETNOT2VAL(sat, unsat, aggs) (not sat && not unsat && aggs.size()>0)

SATVAL PropagatorFactory::finishSet(const WLSet* origset, vector<TempAgg*>& aggs, bool optimagg, uint optimpriority) {
	bool unsat = false, sat = false;

	if(aggs.size()==0){
		return SATVAL::POS_SAT;
	}

	AggProp const * type = NULL;
	switch (aggs.front()->getType()) {
	case AggType::MAX:
		type = AggProp::getMax();
		break;
	case AggType::SUM:
		type = AggProp::getSum();
		break;
	case AggType::CARD:
		type = AggProp::getCard();
		break;
	case AggType::PROD:
		type = AggProp::getProd();
		break;
	default:
		MAssert(false);
		break;
	}

	if(origset->wl.size()==0){
		if(optimagg){
			throw idpexception("An optimization aggregate cannot have an empty set.\n");
		}
		for(auto i=aggs.cbegin(); i<aggs.cend(); ++i){
			if((*i)->hasLB()){
				getEngine().notifySetTrue((type->getESV()>=(*i)->getBound())?(*i)->getHead():not (*i)->getHead());
			}else{
				getEngine().notifySetTrue((type->getESV()<=(*i)->getBound())?(*i)->getHead():not (*i)->getHead());
			}
		}
		aggs.clear();
		return getEngine().satState();
	}

	auto set = new WLSet(*origset);

	// transform into SAT if requested
	if (getEngine().modes().tocnf && not optimagg) {
		if (not AggStorage::hasStorage()) {
			AggStorage::addStorage(getEnginep());
		}
		AggStorage::getStorage()->add(set, aggs);
	}
	if (aggs.size() == 0) {
		return SATVAL::POS_SAT;
	}

	Weight knownbound(0);
	if (not optimagg) { // TODO can we do better for minimization over aggregates?
		if (SETNOT2VAL(sat, unsat, aggs)) {
			setReduce(getEnginep(), set, aggs, *type, knownbound, unsat, sat);
		}
		if (SETNOT2VAL(sat, unsat, aggs)) {
			addHeadImplications(getEnginep(), set, aggs, unsat, sat);
		}
		if (SETNOT2VAL(sat, unsat, aggs)) {
			max2SAT(getEnginep(), set, aggs, unsat, sat);
		}
		if (SETNOT2VAL(sat, unsat, aggs)) {
			card2Equiv(getEnginep(), set, aggs, knownbound, unsat, sat);
		}
		if (SETNOT2VAL(sat, unsat, aggs)) {
			decideUsingWatchesAndCreatePropagators(getEnginep(), set, aggs, knownbound);
		}
	} else {
		if (SETNOT2VAL(sat, unsat, aggs)) {
			MAssert(aggs.size()==1);
			decideUsingWatchesAndCreateMinimizationPropagator(getEnginep(), set, aggs[0], knownbound, optimpriority);
		}
	}

	aggs.clear();

	return unsat ? SATVAL::UNSAT : SATVAL::POS_SAT;
}

SATVAL PropagatorFactory::finishParsing() {
	MAssert(isParsing());
	parsing = false;

	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyEnd();
	}

	// create one, certainly true variable which can act as a dummy head
	dummyvar = getEngine().newVar();
	Disjunction clause;
	clause.literals.push_back(mkLit(dummyvar));
	add(clause);

	SATVAL satval = SATVAL::POS_SAT;

	// create reified aggregates
	for (auto i = parsedaggs.cbegin(); satval == SATVAL::POS_SAT && i != parsedaggs.cend(); ++i) {
		add(Aggregate(dummyvar, (*i)->setID, (*i)->bound, (*i)->type, (*i)->sign, AggSem::COMP, -1));
		satval &= getEngine().satState();
	}
	deleteList<Aggregate>(parsedaggs);

	for (auto i = parsedsets.begin(); satval == SATVAL::POS_SAT && i != parsedsets.end(); ++i) {
		satval &= finishSet((*i).second.set, (*i).second.aggs);
	}
	if (AggStorage::hasStorage()) {
		satval &= execute(*AggStorage::getStorage());
	}

	definitions->addToPropagators();

	return satval;
}

void PropagatorFactory::includeCPModel(std::vector<VariableEqValue>& varassignments) {
	for (auto i = intvars.cbegin(); i != intvars.cend(); ++i) {
		VariableEqValue vareq;
		vareq.variable = (*i).first;
		vareq.value = (*i).second->minValue();
		varassignments.push_back(vareq);
	}
}

void PropagatorFactory::add(const LazyGroundLit& object) {
	MAssert(getEngine().modes().lazy);
	MAssert(not getEngine().isDecisionVar(var(object.residual)));
	// TODO in fact, want to check that it does not yet occur in the theory, this is easiest hack
	if(getEngine().verbosity()>4){
		clog <<toString(object.residual, getEngine()) <<" is delayed " <<(object.watchboth?"on unknown":"on true") <<"\n";
	}
	if (object.watchboth) {
		new LazyResidual(getEnginep(), var(object.residual), object.monitor);
	} else {
		getEngine().getSATSolver()->setInitialPolarity(var(object.residual), not sign(object.residual));
		new LazyResidualWatch(getEnginep(), object.residual, object.monitor);
		//std::clog <<"First choosing " <<mkPosLit(var(object.residual)) <<" " <<(not sign(object.residual)?"true":"false") <<"\n";
	}
}
