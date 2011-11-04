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

#include "modules/CPSolver.hpp"
#include "modules/cpsolver/CPScript.hpp"

#include "modules/cpsolver/CPUtils.hpp"
#include "theorysolvers/PCSolver.hpp"

#include "modules/cpsolver/Constraint.hpp"
#include "modules/cpsolver/CPSolverData.hpp"
#include "utils/Print.hpp"

using namespace std;
using namespace MinisatID;
using namespace Gecode;

//FIXME include cp model in printing of models


LitTrail::LitTrail(){
	trailindexoflevel.push_back(trail.size());
}
void LitTrail::newDecisionLevel(){
	trailindexoflevel.push_back(trail.size());
}
void LitTrail::backtrackDecisionLevels(int untillevel){
	vector<Var>::size_type earliest = trailindexoflevel[(uint)untillevel+1];
	while(trail.size()>earliest){
		values[var(trail.back())] = l_Undef;
		trail.pop_back();
	}

	while(trailindexoflevel.size()>untillevel+1){
		trailindexoflevel.pop_back();
	}
}
void LitTrail::propagate(const Lit& l){
	trail.push_back(l);
	values[var(l)] = sign(l)?l_False:l_True;
}
lbool LitTrail::value(const Lit& l) const{
	map<Var, lbool>::const_iterator it = values.find(var(l));
	if(it==values.cend()){
		return l_Undef;
	}
	return (*it).second;
}

CPSolver::CPSolver(PCSolver * solver):
		Propagator(solver), solverdata(new CPSolverData()),
		searchedandnobacktrack(false),
		savedsearchengine(NULL){

	getPCSolver().accept(this, EV_BACKTRACK);
	getPCSolver().accept(this, EV_DECISIONLEVEL);
	getPCSolver().accept(this, EV_PRINTSTATS);
	getPCSolver().accept(this, EV_PRINTSTATE);
	getPCSolver().acceptFinishParsing(this, false);
}

CPSolver::~CPSolver() {
	delete solverdata;
}

const CPScript&	CPSolver::getSpace() const {
	return getData().getSpace();
}
CPScript& CPSolver::getSpace(){
	return getData().getSpace();
}

TermIntVar CPSolver::convertToVar(uint term) const{
	return getData().convertToVar(term);
}
vtiv CPSolver::convertToVars(const std::vector<uint>& terms) const{
	return getData().convertToVars(terms);
}

// INITIALIZATION

bool CPSolver::add(const InnerIntVarEnum& form){
	assert(!isInitialized());
	getData().addTerm(TermIntVar(getSpace(), form.varID, form.values));
	return true;
}

bool CPSolver::add(const InnerIntVarRange& form){
	assert(!isInitialized());
	getData().addTerm(TermIntVar(getSpace(), form.varID, form.minvalue, form.maxvalue));
	return true;
}

bool CPSolver::add(const InnerCPBinaryRel& form){
	assert(!isInitialized());
	getPCSolver().accept(this, mkNegLit(form.head), SLOW);
	getPCSolver().accept(this, not mkNegLit(form.head), SLOW);
	TermIntVar lhs(convertToVar(form.varID));
	getData().addReifConstraint(new BinArithConstraint(getSpace(), lhs, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPBinaryRelVar& form){
	assert(!isInitialized());
	TermIntVar lhs(convertToVar(form.lhsvarID));
	TermIntVar rhs(convertToVar(form.rhsvarID));
	getPCSolver().accept(this, mkNegLit(form.head), SLOW);
	getPCSolver().accept(this, not mkNegLit(form.head), SLOW);
	getData().addReifConstraint(new BinArithConstraint(getSpace(), lhs, toRelType(form.rel), rhs, form.head));
	return true;
}

bool CPSolver::add(const InnerCPSumWeighted& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	getPCSolver().accept(this, mkNegLit(form.head), SLOW);
	getPCSolver().accept(this, not mkNegLit(form.head), SLOW);
	getData().addReifConstraint(new SumConstraint(getSpace(), set, form.weights, toRelType(form.rel), form.bound, form.head));
	return true;
}

bool CPSolver::add(const InnerCPCount& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	TermIntVar rhs(convertToVar(form.rhsvar));
	getData().addNonReifConstraint(new CountConstraint(getSpace(), set, toRelType(form.rel), form.eqbound, rhs));
	return true;
}

bool CPSolver::add(const InnerCPAllDiff& form){
	assert(!isInitialized());
	vector<TermIntVar> set(convertToVars(form.varIDs));
	getData().addNonReifConstraint(new DistinctConstraint(getSpace(), set));
	return true;
}

// SOLVER METHODS

// Space management:
//		First space = space after adding all constraints and propagating until fixpoint
//		Any subsequent space is after adding ALL propagations of a decision level and propagating until fixpoint
//			so this can be MULTIPLE fixpoint propagations until next decision level!

rClause CPSolver::getExplanation(const Lit& p){
	// IMPORTANT: reason is necessary, because a literal might be derived by CP, but
	// requested an explanation before it is effectively propagated and in the trail itself

	assert(propreason[p]!=-1);

	InnerDisjunction clause;
	clause.literals.push_back(p);
	for(vector<Lit>::size_type i=0; i<propreason[p]; i++){
		// FIXME skip all those not propagated into the cp solver
		clause.literals.push_back(~trail.getTrail()[i]);
	}
	return getPCSolver().createClause(clause, true);
}

rClause CPSolver::notifySATsolverOfPropagation(const Lit& p) {
	if (getPCSolver().value(p) == l_False) {
		if (getPCSolver().verbosity() >= 2) {
			clog <<">> Deriving conflinct in " <<p <<" because of constraint expression.\n";
		}
		vector<Lit>::size_type temp = propreason[p];
		propreason[p] = trail.getTrail().size();
		rClause confl = getExplanation(p);
		propreason[p] = temp;
		return confl;
	} else if (getPCSolver().value(p) == l_Undef) {
		if (getPCSolver().verbosity() >= 2) {
			clog <<">> Deriving " <<p <<" because of constraint expression.\n";
		}
		propreason[p] = trail.getTrail().size();
		getPCSolver().setTrue(p, this);
	} else {
		//NOOP
	}
	return nullPtrClause;
}

void CPSolver::checkHeadUniqueness() const{
	set<Var> heads;
	for(vector<ReifiedConstraint*>::const_iterator i=getData().getReifConstraints().cbegin(); i<getData().getReifConstraints().cend(); i++){
		if(heads.find((*i)->getHead())!=heads.cend()){
			stringstream ss;
			ss <<"Constraint reification atoms should be unique, but " <<(*i)->getHead() <<" is shared by at least two constraints.\n";
			throw idpexception(ss.str());
		}
		heads.insert((*i)->getHead());
	}
}

void CPSolver::finishParsing(bool& present, bool& unsat){
	assert(isParsing() && present && !unsat);
	notifyParsed();

	if(getData().getNonReifConstraints().size() + getData().getReifConstraints().size() + getData().getTerms().size() == 0){
		present = false;
		return;
	}

	checkHeadUniqueness();

	// Propagate until fixpoint
	StatusStatistics stats;
	SpaceStatus status = getSpace().status(stats);

	if(status==SS_FAILED){
		unsat = true;
	}

	// Propagate all assigned reification atoms.
	if(!unsat && propagateReificationConstraints()!=nullPtrClause){
		unsat = true;
	}

	notifyInitialized();

	return;
}

void CPSolver::notifyNewDecisionLevel(){
	getData().addSpace();
	trail.newDecisionLevel();
}

void CPSolver::notifyBacktrack(int untillevel, const Lit& decision){
	//clog <<"Backtracked CP solver.\n";
	getData().removeSpace(untillevel);
	searchedandnobacktrack = false;
	trail.backtrackDecisionLevels(untillevel);
	Propagator::notifyBacktrack(untillevel, decision);
}

rClause CPSolver::notifypropagate(){
	rClause confl = nullPtrClause;

	if(!isInitialized()) { return confl; }
	if(searchedandnobacktrack){ return confl; }

	while(hasNextProp() && confl==nullPtrClause){
		const Lit& l = getNextProp();

		//Check if any constraint matched (might be turned into map)
		ReifiedConstraint* constr = NULL;
		for(reifconstrlist::const_iterator i=getData().getReifConstraints().cbegin(); i<getData().getReifConstraints().cend(); i++){
			if((*i)->getHead()==var(l)){
				constr = *i;
				break;
			}
		}

		if(constr!=NULL){
			if(getPCSolver().modes().verbosity >= 5){
				clog <<">> Propagated into CP: " <<l <<".\n";
			}

			trail.propagate(l);
			if(!constr->isAssigned(getSpace())){
				confl = constr->propagate(!sign(l), getSpace());
			}
		}
	}

	if(confl!=nullPtrClause){
		return confl;
	}

	StatusStatistics stats;
	SpaceStatus status = getSpace().status(stats);

	if(status == SS_FAILED){ //Conflict
		return genFullConflictClause();
	}

	if(verbosity()>=3){
		clog <<"Propagated " <<trail.getTrail().size() <<" of " <<getData().getReifConstraints().size() <<" literals\n";
	}

	if(getData().getReifConstraints().size()==trail.getTrail().size()){
		confl = propagateFinal(false);
		searchedandnobacktrack = true;
	}

	if(confl==nullPtrClause){
		confl = propagateReificationConstraints();
	}

	return confl;
}

/**
 * Very simple clause generation: use all literals that were propagated into the CP solver
 * 		(and which represent reification atoms)
 */
rClause CPSolver::genFullConflictClause(){
	// TEMPORARY CODE: find conflicting propagated literal => start from previous space
	/*reportf("Finding shortest reason \n");
	CPScript& space = *static_cast<CPScript*>(getSolverData()->getPrevSpace().clone());
	space.addBranchers();
	vector<Lit>::const_iterator nonassigned = trail.cbegin();
	int currentlevel = getPCSolver().getLevel(var(trail.back()));
	reportf("Current level: %d\n", currentlevel);
	for(; nonassigned<trail.cend(); nonassigned++){
		if(getPCSolver().getLevel(var(*nonassigned))==currentlevel){
			break;
		}
	}
	for(; nonassigned<trail.cend(); nonassigned++){
		reportf("Possible conflict literal: "); gprintLit(*nonassigned); reportf("\n");
		for(vreifconstrptr::const_iterator i=getSolverData()->getReifConstraints().cbegin(); i<getSolverData()->getReifConstraints().cend(); i++){
			if((*i)->getAtom()==var(*nonassigned) && !(*i)->isAssigned(space)){
				(*i)->propagate(!sign(*nonassigned), space);
				break;
			}
		}

		Search::Options searchOptions_;
		DFS<CPScript>* searchEngine_; // depth first search
		CPScript* enumerator_ = NULL;

		searchOptions_ = Search::Options::def;
		searchOptions_.stop = NULL; //new Search::MemoryStop(1000000000);

		searchEngine_ = new DFS<CPScript>(&space, searchOptions_);
		enumerator_ = searchEngine_->next();

		if(enumerator_==NULL){
			break;
		}
	}
	reportf("Conflicting literal: "); gprintLit(*nonassigned); reportf("\n");*/
	// END

	InnerDisjunction clause;
	for(vector<Lit>::const_reverse_iterator i=trail.getTrail().rbegin(); i<trail.getTrail().rend(); i++){
		//FIXME skip all literals that were propagated BY the CP solver
		clause.literals.push_back(~(*i));
	}
	rClause c = getPCSolver().createClause(clause, true);
	getPCSolver().addLearnedClause(c);
	return c;
}

rClause CPSolver::propagateReificationConstraints(){
	rClause confl = nullPtrClause;
	for(vector<ReifiedConstraint*>::const_iterator i=getData().getReifConstraints().cbegin(); confl==nullPtrClause && i<getData().getReifConstraints().cend(); i++){
		if((*i)->isAssigned(getSpace())){
			confl = notifySATsolverOfPropagation((*i)->isAssignedFalse(getSpace())?mkNegLit((*i)->getHead()):mkPosLit((*i)->getHead()));
		}
	}
	return confl;
}

rClause CPSolver::findNextModel(){
	return propagateFinal(true);
}

rClause CPSolver::propagateFinal(bool usesavedengine){
	rClause confl = nullPtrClause;

	if(!usesavedengine || savedsearchengine == NULL){
		Search::Options searchOptions;

		getSpace().addBranchers();

		searchOptions = Search::Options::def;
		searchOptions.stop = NULL; //new Search::MemoryStop(1000000000);

		savedsearchengine = new DFS<CPScript>(&getSpace(), searchOptions);
	}

	CPScript* enumerator = savedsearchengine->next();

	if(enumerator==NULL){
		if(savedsearchengine->stopped()){
			throw idpexception("memory overflow on CP part");
		}else{
			if(getPCSolver().modes().verbosity>=5){
				clog <<"Conflict found in CP search.\n";
			}
			//FIXME also found if there are no solutions or there are constraints submitted (which should not fail in any case).
			confl = genFullConflictClause();
		}
	}else{
		//clog <<"Model found for CP part.\n";
		if(getData().getReifConstraints().size()==trail.getTrail().size()){ //No @pre guarantee, so check!
			getData().replaceLastWith(enumerator);
			//clog <<getSpace();
		}
	}

	return confl;
}

void CPSolver::getVariableSubstitutions(std::vector<VariableEqValue>& varassignments){
	for(vtiv::const_iterator i=getData().getTerms().cbegin(); i<getData().getTerms().cend(); i++){
		VariableEqValue varass;
		varass.variable = (*i).getID();
		varass.value = (*i).getIntVar(getSpace()).val();
		varassignments.push_back(varass);
	}
}

int	CPSolver::getNbOfFormulas() const {
	return solverdata->getNonReifConstraints().size()*100 + solverdata->getReifConstraints().size()*100;
}

void CPSolver::printStatistics() const{
	//TODO
}

void CPSolver::printState() const{
	//TODO
}
