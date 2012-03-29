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
#include "modules/CPSolver.hpp"
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

void throwNegativeHead(Var head) {
	stringstream ss;
	ss << "An aggregate cannot be defined by a negative head, violated for " << getPrintableVar(head) << ".\n";
	throw idpexception(ss.str());
}

void throwHeadOccursInSet(Var head, int setid) {
	stringstream ss;
	ss << "For the aggregated with head " << getPrintableVar(head) << " also occurs in set " <<setid <<".\n";
	throw idpexception(ss.str());
}

PropagatorFactory::PropagatorFactory(const SolverOption& modes, PCSolver* engine) :
		engine(engine), parsing(true), maxset(1) {
	SATStorage::setStorage(engine->getSATSolver());
	SATStorage::getStorage()->notifyUsedForSearch();
#ifdef CPSUPPORT
	CPStorage::setStorage(engine->getCPSolverp());
	CPStorage::getStorage()->notifyUsedForSearch();
#endif

	if (modes.printcnfgraph) {
		parsingmonitors.push_back(new ECNFGraphPrinter<ostream>(cout));
	}

	if (modes.verbosity > 2) {
		parsingmonitors.push_back(new HumanReadableParsingPrinter<ostream>(clog));
	}

	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyStart();
	}
}

PropagatorFactory::~PropagatorFactory() {
	deleteList<ConstraintVisitor>(parsingmonitors);
	for (auto i = parsedsets.cbegin(); i != parsedsets.cend(); ++i) {
		delete ((*i).second.first);
	}
}

template<typename T>
void PropagatorFactory::notifyMonitorsOfAdding(const T& obj) const {
	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->visit(obj);
	}
}

bool PropagatorFactory::hasIDSolver(defID id) const {
	return idsolvers.find(id) != idsolvers.cend();
}

IDSolver* PropagatorFactory::getIDSolver(defID id) {
	if (!hasIDSolver(id)) {
		addIDSolver(id);
	}
	return idsolvers.at(id);
}

void PropagatorFactory::addIDSolver(defID id) {
	auto idsolver = new IDSolver(getEnginep(), id);
	idsolvers.insert( { id, idsolver });
}

void PropagatorFactory::addVar(Var v, VARHEUR heur) {
	getEngine().createVar(v, heur);
}

void PropagatorFactory::addVar(Lit lit, VARHEUR heur){
	addVar(var(lit), heur);
	/*if(newvar){ // FIXME hack to guarantee that if a literal only occurs positive(negative), it's var is first chosen true(false)
		getEngine().getSATSolver()->setInitialPolarity(var(lit), sign(lit));
		std::clog <<"First choosing " <<lit <<" " <<(sign(lit)?"true":"false") <<"\n";
	}*/
}

void PropagatorFactory::addVars(const vector<Lit>& a, VARHEUR heur) {
	for (auto i = a.cbegin(); i != a.cend(); ++i) {
		addVar(*i, heur);
	}
}

int PropagatorFactory::newSetID() {
	assert(!isParsing());
	return maxset++;
}

void toVec(const std::vector<Lit>& literals, vec<Lit>& lits) {
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		lits.push(*i);
	}
}

// If lazy, do not decide for literals in decisions
// NOTE: only use this if the watches mechanism of the constraint will take care of making literal decidable if necessary
VARHEUR PropagatorFactory::lazyDecide() const {
	return getEngine().modes().lazy ? VARHEUR::DONT_DECIDE : VARHEUR::DECIDE;
}

void PropagatorFactory::add(const InnerDisjunction& clause) {
	notifyMonitorsOfAdding(clause);

	addVars(clause.literals, lazyDecide());

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

// Precondition: already added vars!
void PropagatorFactory::addImplication(const Lit& head, const litlist& body, bool conjunction) {
	if (conjunction) {
		InnerDisjunction d;
		d.literals.resize(2, not head);
		for (auto i = body.cbegin(); i < body.cend(); ++i) {
			d.literals[1] = *i;
			add(d);
		}
	} else {
		InnerDisjunction d;
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

void PropagatorFactory::add(const InnerImplication& formula) {
	// TODO equiv propagator (or 1-watched scheme for the long clause)
	addVar(formula.head, lazyDecide());
	addVars(formula.literals, lazyDecide());

	switch (formula.type) {
	case ImplicationType::EQUIVALENT:
		addImplication(formula.head, formula.literals, formula.conjunctive);
		addReverseImplication(formula.head, formula.literals, formula.conjunctive);
		break;
	case ImplicationType::IMPLIEDBY:
		addReverseImplication(formula.head, formula.literals, formula.conjunctive);
		break;
	case ImplicationType::IMPLIES:
		addImplication(formula.head, formula.literals, formula.conjunctive);
		break;
	}
}

void PropagatorFactory::add(const InnerRule& rule) {
	notifyMonitorsOfAdding(rule);

	addVar(rule.head, lazyDecide());
	addVars(rule.body, lazyDecide());

	getIDSolver(rule.definitionID)->addRule(rule.conjunctive, rule.head, rule.body);
}

void PropagatorFactory::add(const InnerWLSet& formula) {
	notifyMonitorsOfAdding(formula);

	for (auto i = formula.wls.cbegin(); i != formula.wls.cend(); ++i) {
		addVar((*i).getLit());
	}

	if (formula.setID > maxset) {
		maxset = formula.setID;
	}

	if (contains(parsedsets, formula.setID)) {
		throwDoubleDefinedSet(formula.setID);
	}

	// TODO only if type is known here verifySet(formula);

	parsedsets.insert( { formula.setID, SetWithAggs(new InnerWLSet(formula), vector<TempAgg*>()) });
}

void PropagatorFactory::add(const InnerAggregate& agg) {
	notifyMonitorsOfAdding(agg);

	guaranteeAtRootLevel(); // TODO currently only at root level, should change?

	if (parsedsets.find(agg.setID) == parsedsets.cend()) {
		throwUndefinedSet(agg.setID);
	}

	if (isParsing()) {
		parsedaggs.push_back(new InnerAggregate(agg));
	} else {
		InnerReifAggregate r = InnerReifAggregate();
		r.bound = agg.bound;
		r.defID = -1;
		r.head = dummyvar;
		r.sem = AggSem::COMP;
		r.setID = agg.setID;
		r.sign = agg.sign;
		r.type = agg.type;
		add(r);
	}
}

void PropagatorFactory::add(const InnerReifAggregate& origagg) {
	notifyMonitorsOfAdding(origagg);

	guaranteeAtRootLevel(); // TODO currently only at root level, should change?

	InnerReifAggregate newagg(origagg);

	if (parsedsets.find(newagg.setID) == parsedsets.cend()) {
		throwUndefinedSet(newagg.setID);
	}

	addVar(newagg.head);

	auto setwithagg = parsedsets.at(newagg.setID);
	if (setwithagg.second.empty()) {
		setwithagg.first->type = origagg.type;
	}
	if (newagg.type == AggType::MIN) {
		newagg.type = AggType::MAX;
		newagg.sign = newagg.sign == AggSign::LB ? AggSign::UB : AggSign::LB;
		newagg.bound = -newagg.bound;
		if (setwithagg.second.size() == 0) { // FIXME ugly: check whether it is the first MIN agg added to the set
			auto set = setwithagg.first;
			vector<WL> newwls;
			for (auto i = set->getWL().cbegin(); i != set->getWL().cend(); ++i) {
				newwls.push_back(WL((*i).getLit(), -(*i).getWeight()));
			}
			set->wls = newwls;
		}
	}
	if (newagg.sem == AggSem::DEF) {
		getIDSolver(newagg.defID)->addDefinedAggregate(newagg, *setwithagg.first);
	}
	addAggrExpr(newagg.head, newagg.setID, newagg.sign, newagg.bound, newagg.type, newagg.sem);
}

void PropagatorFactory::addAggrExpr(Var head, int setid, AggSign sign, const Weight& bound, AggType type, AggSem sem) {
	assert(type!=AggType::MIN);
	SetWithAggs& set = parsedsets.at(setid);

	if (set.second.size() == 0) { // FIXME add this to the parser and remove it from here
		set.first->type = type;
	}

	verifyAggregate(set.first, head, type);

	getEngine().varBumpActivity(head); // NOTE heuristic! (TODO move)

	auto agg = new TempAgg(mkPosLit(head), AggBound(sign, bound), sem == AggSem::DEF ? AggSem::COMP : sem, type);
	set.second.push_back(agg);

	if (not isParsing()) {
		finishSet(set.first, set.second);
	}
}

void PropagatorFactory::add(const InnerMinimizeSubset& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	addVars(formula.literals);
	getEngine().addOptimization(Optim::SUBSET, formula.literals);
}

void PropagatorFactory::add(const InnerMinimizeOrderedList& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	if (formula.literals.size() == 0) {
		throw idpexception("The set of literals to be minimized is empty.\n");
	}

	addVars(formula.literals);
	getEngine().addOptimization(Optim::LIST, formula.literals);
}
void PropagatorFactory::add(const InnerMinimizeAgg& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	auto head = getEngine().newVar();
	addVar(head);

	InnerDisjunction d;
	d.literals.push_back(mkPosLit(head));
	add(d);

	auto it = parsedsets.find(formula.setID);
	if (it == parsedsets.cend()) {
		throwUndefinedSet(formula.setID);
	}
	auto set = it->second.first;
	set->type = formula.type;

	tempagglist aggs;
	AggBound bound(AggSign::UB, Weight(0));
	// FIXME IMPLICATION IS USED INCORRECTLY (but could be used here!)
	aggs.push_back(new TempAgg(mkPosLit(head), bound, AggSem::COMP, formula.type));
	finishSet(set, aggs, true);
}

void PropagatorFactory::add(const InnerMinimizeVar& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	throw idpexception("MinimizeVar is not handled at the moment"); // FIXME
	// TODO check var existence and add optim intvar to pcsolver
}

void PropagatorFactory::add(const InnerForcedChoices& formula) {
	notifyMonitorsOfAdding(formula);

	guaranteeAtRootLevel();

	if (formula.forcedchoices.size() != 0) {
		vec<Lit> lits;
		toVec(formula.forcedchoices, lits);
		SATStorage::getStorage()->addForcedChoices(lits);
	}
}

void PropagatorFactory::add(const InnerSymmetry& formula) {
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

void PropagatorFactory::add(const InnerIntVarRange& obj) {
	addCP(obj);
	/*if(intvars.find(obj.varID)!=intvars.cend()){
	 stringstream ss;
	 ss <<"Integer variable " <<obj.varID <<" was declared twice.\n";
	 throw idpexception(ss.str());
	 }
	 intvars.insert(pair<int, IntVar*>(obj.varID, new IntVar(getEnginep(), obj.varID, toInt(obj.minvalue), toInt(obj.maxvalue))));*/
}

void PropagatorFactory::add(const InnerIntVarEnum& obj) {
	addCP(obj);
}

void PropagatorFactory::add(const InnerCPBinaryRel& obj) {
	addVar(obj.head);
	addCP(obj);

	/*InnerEquivalence eq;
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

void PropagatorFactory::add(const InnerCPBinaryRelVar& obj) {
	addVar(obj.head);
	addCP(obj);
	//new BinaryConstraint(getEnginep(), intvars.at(obj.lhsvarID), obj.rel, intvars.at(obj.rhsvarID), obj.head);
}

void PropagatorFactory::add(const InnerCPSumWeighted& obj) {
	addVar(obj.head);
	addCP(obj);
}

void PropagatorFactory::add(const InnerCPCount& obj) {
	addCP(obj);
}

void PropagatorFactory::add(const InnerCPAllDiff& obj) {
	addCP(obj);
}

void PropagatorFactory::add(InnerDisjunction& formula, rClause& newclause) {
	notifyMonitorsOfAdding(formula);
	addVars(formula.literals);

	vec<Lit> lits;
	toVec(formula.literals, lits);
	SATStorage::getStorage()->addBinaryOrLargerClause(lits, newclause);
}

void PropagatorFactory::guaranteeAtRootLevel(){
	if(getEngine().getCurrentDecisionLevel()>0){
		getEngine().backtrackTo(0);
	}
}

#define SETNOT2VAL(sat, unsat, aggs) (not sat && not unsat && aggs.size()>0)

SATVAL PropagatorFactory::finishSet(const InnerWLSet* origset, vector<TempAgg*>& aggs, bool optimagg) {
	bool unsat = false, sat = false;

	AggProp const * type = NULL;
	switch (origset->type) {
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
		assert(false);
		break;
	}

	if(origset->wls.size()==0){
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

	auto set = new InnerWLSet(*origset);

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
			assert(aggs.size()==1);
			decideUsingWatchesAndCreateOptimPropagator(getEnginep(), set, aggs[0], knownbound);
		}
	}

	aggs.clear();

	return unsat ? SATVAL::UNSAT : SATVAL::POS_SAT;
}

SATVAL PropagatorFactory::finishParsing() {
	assert(isParsing());
	parsing = false;

	for (auto i = parsingmonitors.cbegin(); i < parsingmonitors.cend(); ++i) {
		(*i)->notifyEnd();
	}

	// create one, certainly true variable which can act as a dummy head
	dummyvar = getEngine().newVar();
	InnerDisjunction clause;
	clause.literals.push_back(mkLit(dummyvar));
	add(clause);

	SATVAL satval = SATVAL::POS_SAT;

	// create reified aggregates
	for (auto i = parsedaggs.cbegin(); satval == SATVAL::POS_SAT && i != parsedaggs.cend(); ++i) {
		InnerReifAggregate r;
		r.bound = (*i)->bound;
		r.defID = -1;
		r.head = dummyvar;
		r.sem = AggSem::COMP;
		r.setID = (*i)->setID;
		r.sign = (*i)->sign;
		r.type = (*i)->type;
		add(r);
		satval &= getEngine().satState();
	}
	deleteList<InnerAggregate>(parsedaggs);

	for (auto i = parsedsets.begin(); satval == SATVAL::POS_SAT && i != parsedsets.end(); ++i) {
		satval &= finishSet((*i).second.first, (*i).second.second);
	}
	if (AggStorage::hasStorage()) {
		satval &= execute(*AggStorage::getStorage());
	}

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

void PropagatorFactory::add(const InnerLazyClause& object) {
	MAssert(getEngine().modes().lazy);
	MAssert(not getEngine().isDecisionVar(var(object.residual)));
	// TODO in fact, want to check that it does not yet occur in the theory, this is easiest hack
	addVar(object.residual, lazyDecide());
	if(getEngine().verbosity()>4){
		clog <<object.residual <<" is delayed " <<(object.watchboth?"on unknown":"on true") <<"\n";
	}
	if (object.watchboth) {
		new LazyResidual(getEnginep(), var(object.residual), object.monitor);
	} else {
		getEngine().getSATSolver()->setInitialPolarity(var(object.residual), not sign(object.residual));
		new LazyResidualWatch(getEnginep(), object.residual, object.monitor);
		//std::clog <<"First choosing " <<mkPosLit(var(object.residual)) <<" " <<(not sign(object.residual)?"true":"false") <<"\n";
	}
}
