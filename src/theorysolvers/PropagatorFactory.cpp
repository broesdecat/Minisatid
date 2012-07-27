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
#include "modules/FDAggConstraint.hpp"
#include "modules/LazyGrounder.hpp"

#ifdef CPSUPPORT
#include "modules/cpsolver/CPSolver.hpp"
#endif

#include "utils/Print.hpp"
#include "external/utils/ContainerUtils.hpp"

#include "constraintvisitors/ECNFGraphPrinter.hpp"
#include "constraintvisitors/HumanReadableParsingPrinter.hpp"

using namespace std;
using namespace MinisatID;

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
	ss << "An aggregate cannot be defined by a negative head, violated for " << head << ".\n";
	throw idpexception(ss.str());
}

void throwHeadOccursInSet(const std::string& head, int setid) {
	stringstream ss;
	ss << "For the aggregated with head " << head << " also occurs in set " << setid << ".\n";
	throw idpexception(ss.str());
}

PropagatorFactory::PropagatorFactory(const SolverOption& modes, PCSolver* engine)
		: engine(engine), definitions(new Definition(engine)), minnewset(-1), finishedparsing(false) {
	SATStorage::setStorage(engine->getSATSolver());
#ifdef CPSUPPORT
	CPStorage::setStorage(engine->getCPSolver());
#endif

	if (modes.verbosity > 2) {
		parsingmonitors.push_back(new HumanReadableParsingPrinter<ostream>(getEnginep(), clog));
	}

	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyStart();
	}
}

PropagatorFactory::~PropagatorFactory() {
	deleteList<ConstraintPrinter>(parsingmonitors);
	for (auto i = parsedsets.cbegin(); i != parsedsets.cend(); ++i) {
		MAssert((*i).second.set!=NULL);
		delete ((*i).second.set);
	}
}

template<typename T>
void PropagatorFactory::notifyMonitorsOfAdding(const T& obj) const {
	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->add(obj);
	}
}

int PropagatorFactory::newSetID() {
	return minnewset--;
}

void PropagatorFactory::add(const Disjunction& clause) {
	notifyMonitorsOfAdding(clause);
	SATStorage::getStorage()->addClause(clause.literals);
}

void PropagatorFactory::add(const Implication& formula) {
	auto clauses = formula.getEquivalentClauses();
	for (auto i = clauses.cbegin(); i < clauses.cend(); ++i) {
		add(*i);
	}
}

void PropagatorFactory::add(const Rule& rule) {
	notifyMonitorsOfAdding(rule);

	definitions->addRule(rule.definitionID, rule.conjunctive, rule.head, rule.body);
}

void PropagatorFactory::add(const WLSet& formula) {
	notifyMonitorsOfAdding(formula);

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

void PropagatorFactory::addAggrExpr(const Lit& head, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem) {
	MAssert(type!=AggType::MIN);
	auto& set = parsedsets.at(setid);

	if (set.aggs.size() == 0) {
		set.type = type;
	}

	verifyAggregate(set.set, set.type, head, type, getEngine());

	getEngine().varBumpActivity(var(head)); // NOTE heuristic! (TODO move)

	auto agg = new TempAgg(head, AggBound(sign, bound), sem == AggSem::DEF ? AggSem::COMP : sem, type);
	set.aggs.push_back(agg);

	if (finishedParsing()) {
		finishSet(set.set, set.aggs);
	}
}

void PropagatorFactory::add(const MinimizeSubset& formula) {
	notifyMonitorsOfAdding(formula);

	getEngine().notifyOptimizationProblem();

	guaranteeAtRootLevel();

	OptimStatement optim(formula.priority, Optim::SUBSET, formula.literals);
	getEngine().addOptimization(optim);
}

void PropagatorFactory::add(const MinimizeOrderedList& formula) {
	notifyMonitorsOfAdding(formula);

	getEngine().notifyOptimizationProblem();

	guaranteeAtRootLevel();

	OptimStatement optim(formula.priority, Optim::LIST, formula.literals);
	getEngine().addOptimization(optim);
}
void PropagatorFactory::add(const MinimizeAgg& formula) {
	notifyMonitorsOfAdding(formula);

	getEngine().notifyOptimizationProblem();

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

	if (it->second.aggs.size() == 0) {
		it->second.type = formula.type;
	}

	verifyAggregate(set, formula.type, mkPosLit(head), formula.type, getEngine());

	tempagglist aggs;
	AggBound bound(AggSign::UB, Weight(0));
	aggs.push_back(new TempAgg(mkNegLit(head), bound, AggSem::OR, formula.type));
	finishSet(set, aggs, true, formula.priority);
}

void PropagatorFactory::add(const MinimizeVar& formula) {
	notifyMonitorsOfAdding(formula);

	if(getEngine().modes().usegecode){
		throw idpexception("Gecode cannot be used to optimize over finite domain variables at the moment");
	}

	getEngine().notifyOptimizationProblem();

	guaranteeAtRootLevel();

	auto it = intvars.find(formula.varID);
	if (it == intvars.cend()) {
		stringstream ss;
		ss << "The CP var " << formula.varID << " has not been declared yet, but is used in an optimization statement.";
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
	MAssert(getEngine().modes().usegecode);
	guaranteeAtRootLevel();
#ifndef CPSUPPORT
	throw idpexception("Adding a finite domain constraint while minisatid was compiled without CP support\n");
#else
	CPStorage::getStorage()->add(formula);
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
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		if (intvars.find(obj.varID) != intvars.cend()) {
			stringstream ss;
			ss << "Integer variable " << obj.varID << " was declared twice.\n";
			throw idpexception(ss.str());
		}
		IntVar* intvar = NULL;
		if(obj.maxvalue-obj.minvalue<1000){ // TODO verify whether this is a good choice
			intvar = new RangeIntVar(getEnginep(), obj.varID, toInt(obj.minvalue), toInt(obj.maxvalue));
		}else{
			intvar = new LazyIntVar(getEnginep(), obj.varID, toInt(obj.minvalue), toInt(obj.maxvalue)); // TODO also for enum variables
		}
		intvars.insert(pair<int, IntVar*>(obj.varID, intvar));
	}
}

void PropagatorFactory::add(const IntVarEnum& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		if (intvars.find(obj.varID) != intvars.cend()) {
			stringstream ss;
			ss << "Integer variable " << obj.varID << " was declared twice.\n";
			throw idpexception(ss.str());
		}
		intvars.insert(pair<int, IntVar*>(obj.varID, new EnumIntVar(getEnginep(), obj.varID, obj.values)));
	}
}

void PropagatorFactory::add(const CPBinaryRel& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		Implication eq(mkPosLit(obj.head), ImplicationType::EQUIVALENT, {}, true);
		auto left = getIntVar(obj.varID);
		auto intbound = toInt(obj.bound);
		switch (obj.rel) {
		case EqType::EQ:
			eq.body.push_back(left->getLEQLit(intbound));
			eq.body.push_back(left->getGEQLit(intbound));
			break;
		case EqType::NEQ:
			eq.conjunction = false;
			eq.body.push_back(~left->getLEQLit(intbound));
			eq.body.push_back(~left->getGEQLit(intbound));
			break;
		case EqType::GEQ:
			eq.body.push_back(left->getGEQLit(intbound));
			break;
		case EqType::G:
			eq.body.push_back(left->getGEQLit(intbound + 1));
			break;
		case EqType::LEQ:
			eq.body.push_back(left->getLEQLit(intbound));
			break;
		case EqType::L:
			eq.body.push_back(left->getLEQLit(intbound - 1));
			break;
		}
		add(eq);
	}
}

void PropagatorFactory::add(const CPBinaryRelVar& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		new BinaryConstraint(getEnginep(), getIntVar(obj.lhsvarID), obj.rel, getIntVar(obj.rhsvarID), obj.head);
	}
}

void PropagatorFactory::add(const CPSumWeighted& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		vector<IntView*> vars;
		for(auto i=obj.varIDs.cbegin(); i<obj.varIDs.cend(); ++i){
			vars.push_back(new IntView(getIntVar(*i), 0));
		}
		new FDAggConstraint(getEnginep(), mkPosLit(obj.head), AggType::SUM, vars, obj.weights, obj.rel, obj.bound);
	}
}

void PropagatorFactory::add(const CPProdWeighted& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		throw notYetImplemented("Products and gecode"); //TODO FIX!
	}else {
		vector<IntView*> vars;
		for(auto i=obj.varIDs.cbegin(); i<obj.varIDs.cend(); ++i){
			vars.push_back(new IntView(getIntVar(*i), 0));
		}
		new FDAggConstraint(getEnginep(), mkPosLit(obj.head), AggType::PROD, vars, obj.prodWeight, obj.rel, obj.bound);
	}
}

void PropagatorFactory::add(const CPCount& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		throw notYetImplemented("No support for handling CPCount without gecode yet.");
	}
}

void PropagatorFactory::add(const CPAllDiff& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		throw notYetImplemented("No support for handling CPAllDiff without gecode yet.");
	}
}

void PropagatorFactory::add(const CPElement& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		throw notYetImplemented("No support for handling CPElement without gecode yet.");
	}
}

void PropagatorFactory::guaranteeAtRootLevel() {
	// FIXME use reverse trail instead!
	if (getEngine().getCurrentDecisionLevel() > 0) {
		getEngine().backtrackTo(0);
	}
}

#define SETNOT2VAL(sat, unsat, aggs) (not sat && not unsat && aggs.size()>0)

SATVAL PropagatorFactory::finishSet(const WLSet* origset, vector<TempAgg*>& aggs, bool optimagg, uint optimpriority) {
	bool unsat = false, sat = false;

	if (aggs.size() == 0) {
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

	if (origset->wl.size() == 0) {
		for (auto i = aggs.cbegin(); i < aggs.cend(); ++i) {
			if ((*i)->hasLB()) {
				getEngine().notifySetTrue((type->getESV() >= (*i)->getBound()) ? (*i)->getHead() : not (*i)->getHead());
			} else {
				getEngine().notifySetTrue((type->getESV() <= (*i)->getBound()) ? (*i)->getHead() : not (*i)->getHead());
			}
		}
		aggs.clear();
		return getEngine().satState();
	}

	auto set = new WLSet(*origset);

	// transform into SAT if requested
	// TODO handle all aggregates in some way!
	if (getEngine().modes().tocnf && not optimagg) {
		if (not AggStorage::hasStorage()) {
			AggStorage::addStorage(getEnginep());
		}
		AggStorage::getStorage()->add(set, aggs);
		if (finishedparsing) { // TODO bit ugly to have to add it here!
			auto satval = execute(*AggStorage::getStorage());
			AggStorage::resetStorage();
			if (satval == SATVAL::UNSAT) {
				return satval;
			}
		}
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
			// TODO check the effect on performance of addheadImpl, card2Equiv and bumpVar of agg heads in AggPropagator::initialize
			//addHeadImplications(getEnginep(), set, aggs, unsat, sat);
		}
		if (SETNOT2VAL(sat, unsat, aggs)) {
			max2SAT(getEnginep(), set, aggs, unsat, sat);
		}
		if (SETNOT2VAL(sat, unsat, aggs)) {
			// TODO check the effect on performance of addheadImpl, card2Equiv and bumpVar of agg heads in AggPropagator::initialize
			//card2Equiv(getEnginep(), set, aggs, knownbound, unsat, sat);
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
	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyEnd();
	}

	// create one, certainly true variable which can act as a dummy head
	if(not finishedparsing){
		dummyvar = getEngine().newVar();
		Disjunction clause;
		clause.literals.push_back(mkLit(dummyvar));
		add(clause);
	}

	SATVAL satval = SATVAL::POS_SAT;

	// create reified aggregates
	for (auto i = parsedaggs.cbegin(); satval == SATVAL::POS_SAT && i != parsedaggs.cend(); ++i) {
		add(Aggregate(mkPosLit(dummyvar), (*i)->setID, (*i)->bound, (*i)->type, (*i)->sign, AggSem::COMP, -1));
		satval &= getEngine().satState();
	}
	deleteList<Aggregate>(parsedaggs);

	for (auto i = parsedsets.begin(); satval == SATVAL::POS_SAT && i != parsedsets.end(); ++i) {
		satval &= finishSet((*i).second.set, (*i).second.aggs);
	}

	if (AggStorage::hasStorage()) {
		satval &= execute(*AggStorage::getStorage());
		AggStorage::resetStorage();
	}

	definitions->addToPropagators();

	finishedparsing = true;
	return satval;
}

void PropagatorFactory::includeCPModel(std::vector<VariableEqValue>& varassignments) {
	for (auto i = intvars.cbegin(); i != intvars.cend(); ++i) {
		VariableEqValue vareq;
		if((*i).second->minValue()!=(*i).second->maxValue()){
			cerr <<"Variable " <<(*i).second->origid() <<"[" <<(*i).second->minValue() <<"," <<(*i).second->maxValue() <<"]" <<" is not assigned.\n";
			MAssert((*i).second->minValue()==(*i).second->maxValue());
		}
		vareq.variable = (*i).second->origid(); // FIXME Correct when it is possible to add internal intvars!
		vareq.value = (*i).second->minValue();
		varassignments.push_back(vareq);
	}
}

void PropagatorFactory::add(const LazyGroundLit& object) {
	MAssert(getEngine().modes().lazy);
	MAssert(not getEngine().isDecisionVar(var(object.residual)));
	// TODO in fact, want to check that it does not yet occur in the theory, this is easiest hack
	if (getEngine().verbosity() > 4) {
		clog << toString(object.residual, getEngine()) << " is delayed " << (object.watchboth ? "on unknown" : "on true") << "\n";
	}
	if (object.watchboth) {
		new LazyResidual(getEnginep(), var(object.residual), object.monitor);
	} else {
		getEngine().getSATSolver()->setInitialPolarity(var(object.residual), not sign(object.residual));
		new LazyResidualWatch(getEnginep(), object.residual, object.monitor);
		//std::clog <<"First choosing " <<mkPosLit(var(object.residual)) <<" " <<(not sign(object.residual)?"true":"false") <<"\n";
	}
}

void PropagatorFactory::add(const LazyGroundImpl& object) {
	MAssert(getEngine().modes().lazy);
	notifyMonitorsOfAdding(object);
	auto headtruesign = sign(object.impl.head);
	switch(object.impl.type){
	case ImplicationType::EQUIVALENT:
		if(object.impl.conjunction){
			getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), not headtruesign);
		}else{
			getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), headtruesign);
		}
		break;
	case ImplicationType::IMPLIES:
		if(object.impl.conjunction){
			getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), not headtruesign);
		}
		break;
	}
	MAssert(grounder2clause.find(object.id)==grounder2clause.cend());
	grounder2clause[object.id] = new LazyTseitinClause(getEnginep(), object.impl, object.monitor, object.id);
}

void PropagatorFactory::add(const LazyAddition& object) {
	notifyMonitorsOfAdding(object);
	grounder2clause[object.ref]->addGrounding(object.list);
}
