/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Marien, K.U.Leuven, Departement
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
#include "modules/symmetry/Symmetry.hpp"
#include "modules/BinConstr.hpp"
#include "modules/FDAggConstraint.hpp"
#include "modules/LazyImplication.hpp"
#include "modules/LazyResidual.hpp"
#include "modules/LazyAtomPropagator.hpp"

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
		: 	Factory("Propagatorfactory"),
		  	engine(engine),
			definitions(new Definition(engine)),
			finishedparsing(false) {
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

void PropagatorFactory::add(const Disjunction& clause) {
	notifyMonitorsOfAdding(clause);
	internalAdd(clause);
}
void PropagatorFactory::internalAdd(const Disjunction& clause) {
	SATStorage::getStorage()->addClause(clause.literals);
}

void PropagatorFactory::add(const Implication& formula) {
	notifyMonitorsOfAdding(formula);
	auto clauses = formula.getEquivalentClauses();
	for (auto i = clauses.cbegin(); i < clauses.cend(); ++i) {
		internalAdd(*i);
	}
}

void PropagatorFactory::add(const Rule& rule) {
	notifyMonitorsOfAdding(rule);

	definitions->addRule(rule.getID(), rule.onlyif, rule.definitionID, rule.conjunctive, rule.head, rule.body);
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
		definitions->addDefinedAggregate(newagg.getID(), newagg, *setwithagg.set);
	}

	MAssert(newagg.type!=AggType::MIN);
	auto& set = parsedsets.at(newagg.setID);

	if (set.aggs.size() == 0) {
		set.type = newagg.type;
	}

	verifyAggregate(set.set, set.type, newagg.head, newagg.type, getEngine());

	getEngine().varBumpActivity(var(newagg.head)); // NOTE heuristic! (TODO move)

	auto newsem = newagg.sem;
	if (newagg.sem == AggSem::DEF) {
		if (newagg.onlyif) {
			newsem = AggSem::OR;
			newagg.head = not newagg.head;
		} else {
			newsem = AggSem::COMP;
		}
	}
	auto agg = new TempAgg(newagg.getID(), newagg.head, AggBound(newagg.sign, newagg.bound), newsem, newagg.type);
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

	auto head = getEngine().newAtom();
	add(Disjunction(DEFAULTCONSTRID, { mkPosLit(head) }));

	auto it = parsedsets.find(formula.setid);
	if (it == parsedsets.cend()) {
		throwUndefinedSet(formula.setid);
	}
	auto set = it->second.set;
	auto type = formula.type;
	if(type==AggType::MIN){
		it->second.type = AggType::MAX;
		type = AggType::MAX;
		for(auto i = set->wl.begin(); i<set->wl.end(); ++i){
			*i = {i->getLit(), -i->getWeight()};
		}
		throw notYetImplemented("Minimizing a minimum aggregate (as this needs either native support for maximization or for minimum aggregates).");
	}

	if (it->second.aggs.size() == 0) {
		it->second.type = formula.type;
	}

	verifyAggregate(set, type, mkPosLit(head), type, getEngine());

	tempagglist aggs;
	AggBound bound(AggSign::UB, Weight(0));
	aggs.push_back(new TempAgg(DEFAULTCONSTRID, mkNegLit(head), bound, AggSem::OR, type));
	finishSet(set, aggs, true, formula.priority);
}

void PropagatorFactory::add(const OptimizeVar& formula) {
	notifyMonitorsOfAdding(formula);

	if (getEngine().modes().usegecode) {
		throw idpexception("Gecode cannot be used to optimize over finite domain variables at the moment");
	}

	getEngine().notifyOptimizationProblem();

	guaranteeAtRootLevel();

	auto it = intvars.find(formula.varID);
	if (it == intvars.cend()) {
		stringstream ss;
		ss << "The CP var " << toString(formula.varID, getEngine()) << " has not been declared yet, but is used in an optimization statement.";
		throw idpexception(ss.str());
	}
	OptimStatement optim(formula.priority, it->second, formula.minimize);
	getEngine().addOptimization(optim);
}

void PropagatorFactory::add(const Symmetry& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	new SymmetryPropagator(getEnginep(), formula);
}

template<class T>
void PropagatorFactory::addCP(const T&
#ifdef CPSUPPORT
		formula
#endif
		) {
	MAssert(getEngine().modes().usegecode);
	guaranteeAtRootLevel();
#ifndef CPSUPPORT
	throw idpexception("Adding a finite domain constraint while minisatid was compiled without CP support\n");
#else
	CPStorage::getStorage()->add(formula);
#endif
}

void PropagatorFactory::add(const IntVarRange& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		if (intvars.find(obj.varID) != intvars.cend()) {
			stringstream ss;
			ss << "Integer variable " << toString(obj.varID, getEngine()) << " was declared twice.\n";
			throw idpexception(ss.str());
		}
		IntVar* intvar = NULL;
		if (not isNegInfinity(obj.minvalue) && not isPosInfinity(obj.maxvalue) && abs(obj.maxvalue - obj.minvalue) < 100) {
			intvar = new RangeIntVar(obj.getID(), getEnginep(), obj.varID, obj.minvalue, obj.maxvalue, obj.partial?obj.possiblynondenoting:getEngine().getFalseLit());
		} else {
			intvar = new LazyIntVar(obj.getID(), getEnginep(), obj.varID, obj.minvalue, obj.maxvalue, obj.partial?obj.possiblynondenoting:getEngine().getFalseLit()); // TODO also for enum variables
		}
		intvars.insert({ obj.varID, new IntView(intvar, intvar->getVarID(), Weight(0)) });
		intvar->finish();
	}
}

void PropagatorFactory::add(const BoolVar&) {
}

void PropagatorFactory::add(const IntVarEnum& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		if (intvars.find(obj.varID) != intvars.cend()) {
			stringstream ss;
			ss << "Integer variable " << toString(obj.varID, getEngine()) << " was declared twice.\n";
			throw idpexception(ss.str());
		}
		auto intvar = new EnumIntVar(obj.getID(), getEnginep(), obj.varID, obj.values, obj.partial?obj.possiblynondenoting:getEngine().getFalseLit());
		intvars.insert( { obj.varID, new IntView(intvar, obj.varID, Weight(0)) });
		intvar->finish();
	}
}

void PropagatorFactory::add(const CPBinaryRel& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(obj);
	} else {
		Implication eq(obj.getID(), obj.head, ImplicationType::EQUIVALENT, { }, true);
		auto left = getIntView(obj.varID, Weight(0));
		switch (obj.rel) {
		case EqType::EQ:
			eq.body.push_back(left->getEQLit(obj.bound));
			break;
		case EqType::NEQ:
			eq.body.push_back(~left->getEQLit(obj.bound));
			break;
		case EqType::GEQ:
			eq.body.push_back(left->getGEQLit(obj.bound));
			break;
		case EqType::G:
			eq.body.push_back(left->getGEQLit(obj.bound + 1));
			break;
		case EqType::LEQ:
			eq.body.push_back(left->getLEQLit(obj.bound));
			break;
		case EqType::L:
			eq.body.push_back(left->getLEQLit(obj.bound - 1));
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
		auto leftint = getIntView(obj.lhsvarID, Weight(0));
		auto rightint = getIntView(obj.rhsvarID, Weight(0));
		new BinaryConstraint(obj.getID(), getEnginep(), leftint, obj.rel, rightint, obj.head);
	}
}

template<class Elem>
Elem PropagatorFactory::createUnconditional(const Elem& obj, Weight neutral){
	// NOTE: Duplicate code with FlatZincParser interface
	Elem newsum(obj);
	newsum.conditions.clear();
	for(uint i=0; i<newsum.varIDs.size(); ++i){
		auto origintvar = getIntView(newsum.varIDs[i], Weight(0));
		auto newcpvarid = getEngine().newID();
		add(IntVarRange(obj.getID(), newcpvarid, min(neutral,origintvar->origMinValue()), max(neutral,origintvar->origMaxValue())));
				// TODO: better make it an enum if 0 if far from the other values?
		newsum.varIDs[i] = newcpvarid;
		auto tseitin0 = getEngine().newAtom();
		auto tseitineq = getEngine().newAtom();
		auto id = newsum.getID();
		add(Disjunction(id, {obj.conditions[i], mkPosLit(tseitin0)}));
		add(CPBinaryRel(id, mkPosLit(tseitin0), newcpvarid, EqType::EQ, 0));
		add(Disjunction(id, {~obj.conditions[i], mkPosLit(tseitineq)}));
		add(CPBinaryRelVar(id, mkPosLit(tseitineq), newcpvarid, EqType::EQ, newsum.varIDs[i]));
	}
	return newsum;
}

IntView* PropagatorFactory::getIntView(VarID varID, Weight bound){
	if (intvars.find(varID) == intvars.cend()) {
		throw idpexception("Integer variable was not declared before use.\n");
	}
	auto var = intvars.at(varID);
	if(bound==var->getFixedDiff()){
		return var;
	}
	auto id = getEngine().newID();
	return new IntView(var->var(), id, var->getFixedDiff()+bound);
}

void PropagatorFactory::add(const CPSumWeighted& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(createUnconditional(obj, 0));
	} else {
		auto allknown = true;
		for(auto varid : obj.varIDs){
			auto var = getIntView(varid, Weight(0));
			if((var->isPartial() && not var->certainlyHasImage()) || var->origMinValue()!=var->origMaxValue()){
				allknown = false;
				break;
			}
		}
		if(allknown){
			WLSet set(getEngine().newSetID());
			for(uint i=0; i<obj.varIDs.size(); ++i){
				set.wl.push_back({obj.conditions[i], getIntView(obj.varIDs[i], Weight(0))->origMinValue() * obj.weights[i]});
			}
			add(set);
			switch(obj.rel){
			case EqType::EQ:{
				auto ts1 = mkPosLit(getEngine().newAtom()), ts2 = mkPosLit(getEngine().newAtom());
				add(Aggregate(obj.getID(), ts1, set.setID, obj.bound, AggType::SUM, AggSign::LB, AggSem::COMP, -1, false));
				add(Aggregate(obj.getID(), ts2, set.setID, obj.bound, AggType::SUM, AggSign::UB, AggSem::COMP, -1, false));
				add(Implication(obj.getID(), obj.head, ImplicationType::EQUIVALENT, {ts1, ts2}, true));
				break;}
			case EqType::NEQ:{
				auto ts1 = mkPosLit(getEngine().newAtom()), ts2 = mkPosLit(getEngine().newAtom());
				add(Aggregate(obj.getID(), ts1, set.setID, obj.bound+1, AggType::SUM, AggSign::LB, AggSem::COMP, -1, false));
				add(Aggregate(obj.getID(), ts2, set.setID, obj.bound-1, AggType::SUM, AggSign::UB, AggSem::COMP, -1, false));
				add(Implication(obj.getID(), obj.head, ImplicationType::EQUIVALENT, {ts1, ts2}, false));
				break;}
			case EqType::GEQ:
				add(Aggregate(obj.getID(), obj.head, set.setID, obj.bound, AggType::SUM, AggSign::LB, AggSem::COMP, -1, false));
				break;
			case EqType::LEQ:
				add(Aggregate(obj.getID(), obj.head, set.setID, obj.bound, AggType::SUM, AggSign::UB, AggSem::COMP, -1, false));
				break;
			case EqType::L:
				add(Aggregate(obj.getID(), obj.head, set.setID, obj.bound-1, AggType::SUM, AggSign::UB, AggSem::COMP, -1, false));
				break;
			case EqType::G:
				add(Aggregate(obj.getID(), obj.head, set.setID, obj.bound+1, AggType::SUM, AggSign::LB, AggSem::COMP, -1, false));
				break;
			}
		}else{
			vector<IntView*> vars;
			litlist conditions;
			for (size_t i=0; i< obj.varIDs.size(); ++i) {
				auto var = getIntView(obj.varIDs[i], 0);
				vars.push_back(var);
				if(not var->isPartial()){
					conditions.push_back(obj.conditions[i]);
				}else{
					conditions.push_back(mkPosLit(getEngine().newAtom()));
					add(Implication(obj.getID(), conditions[i], ImplicationType::EQUIVALENT, {obj.conditions[i], not var->getNoImageLit()}, true));
				}
			}
			new FDSumConstraint(obj.getID(), getEnginep(), obj.head, conditions, vars, obj.weights, obj.rel, obj.bound);
		}
	}
}

void PropagatorFactory::add(const CPProdWeighted& obj) {
	notifyMonitorsOfAdding(obj);
	if (getEngine().modes().usegecode) {
		addCP(createUnconditional(obj, 1));
	} else {
		vector<IntView*> vars;
		litlist conditions;
		for (size_t i=0; i< obj.varIDs.size(); ++i) {
			auto var = getIntView(obj.varIDs[i], 0);
			vars.push_back(var);
			if(not var->isPartial()){
				conditions.push_back(obj.conditions[i]);
			}else{
				conditions.push_back(mkPosLit(getEngine().newAtom()));
				add(Implication(obj.getID(), conditions[i], ImplicationType::EQUIVALENT, {obj.conditions[i], not var->getNoImageLit()}, true));
			}
		}
		new FDProdConstraint(obj.getID(), getEnginep(), obj.head, conditions, vars, obj.prodWeight, obj.rel, getIntView(obj.boundID, 0));
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

// NOTE: need to guarantee that constraints are never added at a level where they will not have full effect.
// E.g. if propagation is done, but could in fact have been done at earlier level and is not rechecked when backtracking.
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
	if ((getEngine().modes().tocnf || (set->wl.size() < 4 && aggs.size() < 3)) && not optimagg) {
		if (not AggStorage::hasStorage()) {
			AggStorage::addStorage(getEnginep());
		}
		AggStorage::getStorage()->add(set, aggs);
		if (finishedparsing) { // TODO bit ugly to have to add it here!
			auto storage = AggStorage::getStorage();
			AggStorage::clearStorage();
			auto satval = execute(*storage);
			delete (storage);
			if (satval == SATVAL::UNSAT) {
				return satval;
			}
		}
	}
	if (aggs.size() == 0) {
		return SATVAL::POS_SAT;
	}

	if (not optimagg) { // TODO can we do better for minimization over aggregates?
		if (SETNOT2VAL(sat, unsat, aggs)) {
			setReduce(getEnginep(), set, *type);
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
			decideUsingWatchesAndCreatePropagators(getEnginep(), set, aggs);
		}
	} else {
		if (SETNOT2VAL(sat, unsat, aggs)) {
			MAssert(aggs.size()==1);
			decideUsingWatchesAndCreateMinimizationPropagator(getEnginep(), set, aggs[0], optimpriority);
		}
	}

	aggs.clear();

	delete(set);

	return unsat ? SATVAL::UNSAT : SATVAL::POS_SAT;
}

SATVAL PropagatorFactory::finish() {
	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyEnd();
	}

	SATVAL satval = SATVAL::POS_SAT;

	// create reified aggregates
	for (auto i = parsedaggs.cbegin(); satval == SATVAL::POS_SAT && i != parsedaggs.cend(); ++i) {
		add(Aggregate((*i)->getID(), getEngine().getTrueLit(), (*i)->setID, (*i)->bound, (*i)->type, (*i)->sign, AggSem::COMP, -1, false));
		satval &= getEngine().satState();
	}
	deleteList<Aggregate>(parsedaggs);

	for (auto i = parsedsets.begin(); satval == SATVAL::POS_SAT && i != parsedsets.end(); ++i) {
		satval &= finishSet((*i).second.set, (*i).second.aggs);
	}

	if (AggStorage::hasStorage()) {
		auto storage = AggStorage::getStorage();
		AggStorage::clearStorage();
		satval &= execute(*storage);
		delete (storage);
	}

	definitions->addToPropagators();

	finishedparsing = true;
	return satval;
}

void PropagatorFactory::includeCPModel(std::vector<VariableEqValue>& varassignments) {
	for (auto name2var : intvars) {
		auto ivar = name2var.second;
		auto image = ivar->possiblyHasImage();
		if (image && ivar->minValue() != ivar->maxValue()) {
			cerr << "Variable " << ivar->toString() << "[" << ivar->minValue() << "," << ivar->maxValue() << "]" << " is not assigned.\n";
			throw idpexception("Current interpretation is a not a model.");
		}
		varassignments.push_back({ivar->getVarID(), image?ivar->minValue():0, image});
	}
}

template<class Engine>
void PropagatorFactory::propagateAfterAddition(int ID, Engine& engine){
	auto confl = engine.propagate();
	if(confl!=nullPtrClause){
		litlist lits;
		for(uint i=0; i<engine.getClauseSize(confl); ++i){
			lits.push_back(engine.getClauseLit(confl, i));
		}
		add(Disjunction(ID, lits));
	}
}

void PropagatorFactory::add(const LazyGroundLit& object) {
	MAssert(getEngine().modes().lazy);
	notifyMonitorsOfAdding(object);

	if (getEngine().verbosity() > 4) {
		clog << toString(object.residual, getEngine()) << " is delayed on " << object.watchedvalue << "\n";
	}
	if(getEngine().modes().lazyheur){
		getEngine().getSATSolver()->setInitialPolarity(object.residual, object.watchedvalue != Value::True);
	}
	new LazyResidual(getEnginep(), object.residual, object.watchedvalue, object.monitor);

	propagateAfterAddition(0, getEngine());
}

void PropagatorFactory::add(const LazyGroundImpl& object) {
	MAssert(getEngine().modes().lazy);
	notifyMonitorsOfAdding(object);

	auto headtruesign = sign(object.impl.head);
	if(getEngine().modes().lazyheur){
		switch (object.impl.type) {
		case ImplicationType::EQUIVALENT:
			if (object.impl.conjunction) {
				getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), headtruesign);
			} else {
				getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), not headtruesign);
			}
			break;
		case ImplicationType::IMPLIES:
			if (object.impl.conjunction) {
				getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), headtruesign);
			}
			break;
		case ImplicationType::IMPLIEDBY:
			if (not object.impl.conjunction) {
				getEngine().getSATSolver()->setInitialPolarity(var(object.impl.head), not headtruesign);
			}
			break;
		}
	}

	auto clauseid = grounder2clause.size();
	grounder2clause.push_back(new LazyTseitinClause(object.getID(), getEnginep(), object.impl, object.monitor, clauseid));

	propagateAfterAddition(object.getID(), getEngine());
}

void PropagatorFactory::add(const LazyAddition& object) {
	notifyMonitorsOfAdding(object);

	MAssert(object.ref>=0 && grounder2clause.size()>(uint)object.ref);
	for (auto lit : object.list) {
		getEngine().getSATSolver()->setInitialPolarity(var(lit), not sign(lit));
	}
	grounder2clause[object.ref]->addGrounding(object.list);

	propagateAfterAddition(0, getEngine());
}

void PropagatorFactory::add(const TwoValuedRequirement& object) {
	notifyMonitorsOfAdding(object);

	for (auto atom : object.atoms) {
		getEngine().getSATSolver()->setDecidable(atom, true);
	}
	getEngine().addOutputVars(object.atoms);
}

void PropagatorFactory::add(const LazyAtom& object) {
	notifyMonitorsOfAdding(object);

	if(getEngine().modes().usegecode){
		throw idpexception("Gecode does not support lazily expanded atoms yet.");
	}
	std::vector<IntView*> argvars;
	for (auto arg : object.args) {
		argvars.push_back(getIntView(arg, 0));
	}
	new LazyAtomPropagator(object.getID(), getEnginep(), object.head, argvars, object.grounder);

	propagateAfterAddition(object.getID(), getEngine());
}
