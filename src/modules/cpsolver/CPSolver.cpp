/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include <set>
#include <map>

#include "CPSolver.hpp"
#include "CPScript.hpp"

#include "CPUtils.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "Constraint.hpp"
#include "CPSolverData.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Gecode;

LitTrail::LitTrail() {
	newDecisionLevel();
}
void LitTrail::newDecisionLevel() {
	trailindexoflevel.push_back(trail.size());
}
void LitTrail::backtrackDecisionLevels(int untillevel) {
	vector<Atom>::size_type earliest = trailindexoflevel[(uint) untillevel + 1];
	while (trail.size() > earliest) {
		trail.pop_back();
	}

	while (trailindexoflevel.size() > (uint) (untillevel + 1)) {
		trailindexoflevel.pop_back();
	}
}
void LitTrail::propagate(const Lit& l) {
	trail.push_back(l);
}

CPSolver::CPSolver(PCSolver * solver)
		: 	Propagator(DEFAULTCONSTRID, solver, "CP-solver"),
			solverdata(new CPSolverData()),
			addedconstraints(false),
			searchedandnobacktrack(false),
			savedsearchengine(NULL),
			model(NULL),
			searchstarted(false) {
	getPCSolver().accept(this);
	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_DECISIONLEVEL);
	getPCSolver().accept(this, EV_STATEFUL);
	getPCSolver().accept(this, EV_MODELFOUND);

	level2hasspace.push_back(true);
}

CPSolver::~CPSolver() {
	delete solverdata;
}

const CPScript& CPSolver::getSpace() const {
	return getData().getSpace();
}
CPScript& CPSolver::getSpace() {
	return getData().getSpace();
}

TermIntVar CPSolver::convertToVar(VarID term) const {
	return getData().convertToVar(term);
}
std::vector<TermIntVar> CPSolver::convertToVars(const std::vector<VarID>& terms) const {
	return getData().convertToVars(terms);
}

// Constraint addition

bool CPSolver::add(const IntVarEnum& form) {
	vector<int> values;
	for (auto val : form.values) {
		values.push_back(toInt(val));
	}
	getData().addTerm(TermIntVar(getSpace(), form.varID, values));
	return true;
}

bool CPSolver::add(const IntVarRange& form) {
	getData().addTerm(TermIntVar(getSpace(), form.varID, toInt(form.minvalue), toInt(form.maxvalue)));
	return true;
}

bool CPSolver::add(const CPBinaryRel& form) {
	TermIntVar lhs(convertToVar(form.varID));
	add(new BinArithConstraint(getSpace(), lhs, toRelType(form.rel), toInt(form.bound), form.head.getAtom()));
	return true;
}

bool CPSolver::add(const CPBinaryRelVar& form) {
	TermIntVar lhs(convertToVar(form.lhsvarID));
	TermIntVar rhs(convertToVar(form.rhsvarID));
	add(new BinArithConstraint(getSpace(), lhs, toRelType(form.rel), rhs, form.head.getAtom()));
	return true;
}

bool CPSolver::add(const CPSumWeighted& form) {
	MAssert(form.conditions.empty());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	vector<int> values;
	for (auto i = form.weights.cbegin(); i < form.weights.cend(); ++i) {
		values.push_back(toInt(*i));
	}
	add(new SumConstraint(getSpace(), set, values, toRelType(form.rel), toInt(form.bound), form.head.getAtom()));
	return true;
}

bool CPSolver::add(const CPProdWeighted& form) {
	MAssert(form.conditions.empty());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	auto id=getPCSolver().newID();
	if(form.prodWeight!=Weight(1)){
		add(IntVarRange(DEFAULTCONSTRID, id,form.prodWeight, form.prodWeight));
		set.push_back(convertToVar(id));
	}

	if(set.size()!=2 || form.rel!=EqType::EQ){
		throw idpexception("Product of sets is currently not implemented");
	}
	add(new ProdConstraint(getSpace(), set[0], set[1], convertToVar(form.boundID), form.head.getAtom()));
	return true;
}

bool CPSolver::add(const CPCount& form) {
	vector<TermIntVar> set(convertToVars(form.varIDs));
	TermIntVar rhs(convertToVar(form.rhsvar));
	add(new CountConstraint(getSpace(), set, toRelType(form.rel), toInt(form.eqbound), rhs));
	return true;
}

bool CPSolver::add(const CPAllDiff& form) {
	vector<TermIntVar> set(convertToVars(form.varIDs));
	add(new DistinctConstraint(getSpace(), set));
	return true;
}

bool CPSolver::add(const CPElement& form) {
	vector<TermIntVar> set(convertToVars(form.varIDs));
	add(new ElementConstraint(getSpace(), set, convertToVar(form.index), convertToVar(form.rhs)));
	return true;
}

void CPSolver::checkHeadUniqueness(ReifiedConstraint const * const c) {
	if (heads.find(c->getHead()) != heads.cend()) {
		stringstream ss;
		ss << "Constraint reification atoms should be unique, but " << toString(c->getHead()) << " is shared by at least two constraints.\n";
		throw idpexception(ss.str());
	}
	heads.insert(c->getHead());
}

void CPSolver::add(ReifiedConstraint* c) {
	checkHeadUniqueness(c);
	getPCSolver().accept(this, mkNegLit(c->getHead()), SLOW);
	getPCSolver().accept(this, not mkNegLit(c->getHead()), SLOW);
	getData().addReifConstraint(c);

	getPCSolver().accept(this, mkPosLit(c->getHead()), PRIORITY::SLOW);
	getPCSolver().accept(this, mkNegLit(c->getHead()), PRIORITY::SLOW);

	recentreifconstr.push(c);
	savedsearchengine = NULL;

	addedConstraint();
}

void CPSolver::add(NonReifiedConstraint* c) {
	getData().addNonReifConstraint(c);

	addedConstraint();
}

void CPSolver::addedConstraint() {
	addedconstraints = true;
	searchedandnobacktrack = false;

	auto confl = notifypropagate();

	if (confl != nullPtrClause) {
		getPCSolver().notifyUnsat(); // TODO throw unsat with unsat clause?
	}
}

// SOLVER METHODS

void CPSolver::accept(ConstraintVisitor& visitor) {
	getSpace().accept(visitor);
	for (auto constr : getData().getNonReifConstraints()) {
		constr->accept(visitor);
	}
	for (auto cc : getData().getReifConstraints()) {
		cc.second->accept(visitor);
	}
}

// Space management:
//		First space = space after adding all constraints and propagating until fixpoint
//		Any subsequent space is after adding ALL propagations of a decision level and propagating until fixpoint
//			so this can be MULTIPLE fixpoint propagations until next decision level!

rClause CPSolver::getExplanation(const Lit& p) {
	// IMPORTANT: reason is necessary, because a literal might be derived by CP, but
	// requested an explanation before it is effectively propagated and in the trail itself

	MAssert(propreason[p]!=(uint)-1);

	Disjunction clause(DEFAULTCONSTRID, {p});
	for (uint i = 0; i < propreason[p]; i++) {
		// FIXME skip all those not propagated into the cp solver
		clause.literals.push_back(~trail.getTrail()[i]);
	}
	return getPCSolver().createClause(clause, true);
}

rClause CPSolver::notifySATsolverOfPropagation(const Lit& p) {
	if (getPCSolver().value(p) == l_False) {
		if (getPCSolver().verbosity() > 2) {
			clog << ">> Deriving conflict in " << toString(p) << " because of constraint expression.\n";
		}
		auto temp = propreason[p];
		propreason[p] = trail.getTrail().size();
		auto confl = getExplanation(p);
		propreason[p] = temp;
		return confl;
	} else if (getPCSolver().value(p) == l_Undef) {
		if (getPCSolver().verbosity() > 2) {
			clog << ">> Deriving " << toString(p) << " because of constraint expression.\n";
		}
		propreason[p] = trail.getTrail().size();
		getPCSolver().setTrue(p, this);
	} else { // literal was already true
		//NOOP
	}
	return nullPtrClause;
}

void CPSolver::notifyNewDecisionLevel() {
	searchstarted = true;
	level2hasspace.push_back(false);
	trail.newDecisionLevel();
}

void CPSolver::notifyBacktrack(int untillevel, const Lit& decision) {
	for(auto i=level2hasspace.size()-1; i>untillevel; i--){
		if(level2hasspace[i]){
			getData().removeSpace();
		}
	}
	level2hasspace.resize(untillevel+1);

	searchedandnobacktrack = false;
	trail.backtrackDecisionLevels(untillevel);
	Propagator::notifyBacktrack(untillevel, decision);

	savedsearchengine = NULL;
	model = NULL;
}

rClause CPSolver::notifypropagate() {
	auto confl = nullPtrClause;

	if (searchedandnobacktrack) {
		return confl;
	}

	while (hasNextProp() && confl == nullPtrClause) {
		auto l = getNextProp();

		auto constrit = getData().getReifConstraints().find(var(l));
		if(constrit==getData().getReifConstraints().cend()){
			continue;
		}

		if(not level2hasspace[getPCSolver().getCurrentDecisionLevel()]){
			level2hasspace[getPCSolver().getCurrentDecisionLevel()] = true;
			getData().addSpace();
		}

		if (getPCSolver().modes().verbosity >= 5) {
			clog << ">> Propagated into CP: " << toString(l) << ".\n";
		}

		auto constr = constrit->second;
		if (not constr->isAssigned(getSpace())) {
			confl = constr->propagate(!sign(l), getSpace());
		}

		trail.propagate(l);
	}

	while(not recentreifconstr.empty()){ // NOTE: to handle that the head might also have been known the moment the constraint was added, so was already on trail.
		auto constr = recentreifconstr.front();
		recentreifconstr.pop();

		auto lit = mkPosLit(constr->getHead());
		if(not isUnknown(lit) && not constr->isAssigned(getSpace())){
			if(isFalse(lit)){
				lit = ~lit;
			}
			confl = constr->propagate(!sign(lit), getSpace());
		}
	}

	if (confl != nullPtrClause || not level2hasspace[getPCSolver().getCurrentDecisionLevel()]) {
		return confl;
	}

	StatusStatistics stats;
	SpaceStatus status = getSpace().status(stats);

	if (status == SS_FAILED) { //Conflict
		auto c = genFullConflictClause();
		getPCSolver().addConflictClause(c);
		return c;
	}

	if (verbosity() >= 3) {
		clog << "Propagated " << trail.getTrail().size() << " of " << getData().getReifConstraints().size() << " literals\n";
	}

	if(searchstarted && getData().getReifConstraints().size() == trail.getTrail().size()) {
		confl = propagateFinal(false);
		searchedandnobacktrack = true;
	}

	if (confl == nullPtrClause) {
		confl = propagateReificationConstraints();
	}

	return confl;
}

/**
 * Very simple clause generation: use all literals that were propagated into the CP solver
 * 		(and which represent reification atoms)
 */
rClause CPSolver::genFullConflictClause() {
	Disjunction clause(DEFAULTCONSTRID, {});
	for (auto i = trail.getTrail().rbegin(); i < trail.getTrail().rend(); i++) {
		// TODO can skip all literals that were propagated BY the CP solver
		clause.literals.push_back(~(*i));
	}
	return getPCSolver().createClause(clause, true);
}

rClause CPSolver::propagateReificationConstraints() {
	auto confl = nullPtrClause;
	for (auto cc : getData().getReifConstraints()) {
		auto constr = cc.second;
		if (constr->isAssigned(getSpace())) {
			confl = notifySATsolverOfPropagation(constr->isAssignedFalse(getSpace()) ? mkNegLit(constr->getHead()) : mkPosLit(constr->getHead()));
			if(confl!=nullPtrClause){
				break;
			}
		}
	}
	return confl;
}

bool CPSolver::hasData() const {
	return getData().getTerms().size() > 0;
}

int CPSolver::getNbOfFormulas() const {
	return getData().getTerms().size();
}

rClause CPSolver::notifyFullAssignmentFound(){
	searchstarted = true;
	return propagateFinal(false);
}

rClause CPSolver::findNextModel() {
	return propagateFinal(true);
}

rClause CPSolver::propagateFinal(bool findnext) {
	rClause confl = nullPtrClause;
	if (not hasData()) {
		return confl;
	}

	if (!findnext || savedsearchengine == NULL) {
		Search::Options searchOptions;

		getSpace().addBranchers();

		searchOptions = Search::Options::def;
		searchOptions.stop = NULL; //new Search::MemoryStop(1000000000);

		savedsearchengine = new DFS<CPScript>(&getSpace(), searchOptions);
	}

	auto enumerator = savedsearchengine->next();

	if (enumerator == NULL) {
		if (savedsearchengine->stopped()) {
			throw idpexception("memory overflow on CP part");
		} else {
			if (getPCSolver().modes().verbosity >= 5) {
				clog << "Conflict found in CP search.\n";
			}
			confl = genFullConflictClause();
			if (not findnext) {
				getPCSolver().addConflictClause(confl);
			}
		}
	} else{
		model = enumerator;
	}

	return confl;
}

void CPSolver::getVariableSubstitutions(std::vector<VariableEqValue>& varassignments) {
	MAssert(model!=NULL);
	for (auto term : getData().getTerms()) {
		varassignments.push_back(VariableEqValue{term.first,term.second.getIntVar(*model).val()});
	}
}
