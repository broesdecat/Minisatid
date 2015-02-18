/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */

#include "space/SearchEngine.hpp"

#include "theorysolvers/PCSolver.hpp"
#include "modules/ModSolver.hpp"

using namespace MinisatID;
using namespace std;

SearchEngine::~SearchEngine(){
	for(auto solver: solvers){
		delete(solver.second);
	}
}

Factory& SearchEngine::getFactory(TheoryID theoryID) {
	return getSolver(theoryID)->getFactory(theoryID);
}
void SearchEngine::createVar(Atom v, TheoryID theoryID) {
	getSolver(theoryID)->createVar(v, theoryID);
}

int SearchEngine::verbosity() const {
	return getSolver()->verbosity();
}
const SolverOption& SearchEngine::modes() const {
	return getSolver()->modes();
}
Atom SearchEngine::newAtom() {
	return getSolver()->newAtom();
}
int SearchEngine::newSetID() {
	return getSolver()->newSetID();
}
lbool SearchEngine::rootValue(Lit p) const {
	return getSolver()->rootValue(p);
}
Lit SearchEngine::getTrueLit() const {
	return getSolver()->getTrueLit();
}
Lit SearchEngine::getFalseLit() const {
	return getSolver()->getFalseLit();
}

void SearchEngine::notifyUnsat() {
	getSolver()->notifyUnsat();
}
SATVAL SearchEngine::satState() const {
	return getSolver()->satState();
}
bool SearchEngine::isUnsat() const {
	return getSolver()->isUnsat();
}
void SearchEngine::setString(const Atom& lit, const std::string& name){
	return getSolver()->setString(lit, name);
}
std::string SearchEngine::toString(VarID id) const {
	return getSolver()->toString(id);
}
std::string SearchEngine::toString(const Lit& lit) const {
	return getSolver()->toString(lit);
}

bool SearchEngine::isTseitin(const Atom& atom) const {
	return getSolver()->isTseitin(atom);
}

void SearchEngine::invalidate(litlist& clause) const {
	getSolver()->invalidate(clause);
}

void SearchEngine::finishParsing() {
	for(auto solver: solvers){
		solver.second->finishParsing();
	}
	for(auto solver: modsolvers){
		solver->finishParsing();
	}
}
bool SearchEngine::isOptimizationProblem() const {
	return getSolver()->isOptimizationProblem();
}
bool SearchEngine::hasNextOptimum() const {
	return getSolver()->hasNextOptimum();
}
OptimStatement& SearchEngine::getNextOptimum() {
	return getSolver()->getNextOptimum();
}

void SearchEngine::notifyTerminateRequested() {
	getSolver()->notifyTerminateRequested();
}

void SearchEngine::getOutOfUnsat(){
  getSolver()->getOutOfUnsat();
}

std::shared_ptr<Model> SearchEngine::getModel() {
	return getSolver()->getModel();
}
lbool SearchEngine::getModelValue(const Lit& v) {
	return getSolver()->getModelValue(v);
}
lbool SearchEngine::getModelValue(Atom v) {
	return getSolver()->getModelValue(v);
}
MXStatistics SearchEngine::getStats() const{
	return getSolver()->getStats();
}

void SearchEngine::accept(ConstraintVisitor& visitor) {
	getSolver()->accept(visitor);
}

void SearchEngine::addAssumption(const Lit assump){
  createVar(var(assump),getBaseTheoryID());
  getSolver()->addAssumption(assump);
}
void SearchEngine::removeAssumption(const Lit assump){
  createVar(var(assump),getBaseTheoryID());
  getSolver()->removeAssumption(assump);
}
void SearchEngine::clearAssumptions(){
  getSolver()->clearAssumptions();
}
void SearchEngine::addAssumptions(const litlist& assumps) {
	for(auto l: assumps){
		addAssumption(l);
	}
}
lbool SearchEngine::solve(bool search) {
	return getSolver()->solve(search);
}
litlist SearchEngine::getUnsatExplanation() const{
	return getSolver()->getUnsatExplanation();
}

litlist SearchEngine::getEntailedLiterals() const {
	return getSolver()->getEntailedLiterals();
}
bool SearchEngine::moreModelsPossible() const {
	return getSolver()->moreModelsPossible();
}

//Get information on hierarchy
void SearchEngine::checkHasSolver(TheoryID level) const {
	if (not hasSolver(level)) {
		std::stringstream ss;
		ss << ">> No modal operator with id " << level.id << " was declared.";
		throw idpexception(ss.str());
	}
}
bool SearchEngine::hasSolver(TheoryID level) const {
	return solvers.find(level)!=solvers.cend();
}
PCSolver* SearchEngine::getSolver() const{
	return solvers.at({1});
}
PCSolver* SearchEngine::getSolver(TheoryID level) const {
	checkHasSolver(level);
	return solvers.at(level);
}
// FIXME also include these when printing the full theory
void SearchEngine::add(const SubTheory& subtheory){
	// FIXME getSolver()->getFactory().notifyMonitorsOfAdding(subtheory);
	if(hasSolver(subtheory.childid.id)){
		std::stringstream ss;
		ss << ">> A modal operator on level " << subtheory.childid.id << " was already declared.";
		throw idpexception(ss.str());
	}
	if(modes().verbosity>3){
		clog <<"Creating model operator on level " <<subtheory.childid.id <<" with head " <<getSolver()->toString(mkPosLit(subtheory.head));
		clog <<" containing rigid atoms ";
		for(auto atom:subtheory.rigidatoms){
			clog <<getSolver()->toString(mkPosLit(atom)) <<" ";
		}
		clog <<"\n";
	}
	solvers[subtheory.childid] = new PCSolver(subtheory.childid, modes(), NULL, getSolver()->getVarCreator(), this, false);
	MAssert(solvers[subtheory.childid]->getTheoryID()==subtheory.childid);
	modsolvers.insert(new ModSolver(subtheory.head, getSolver(subtheory.theoryid), getSolver(subtheory.childid), subtheory.rigidatoms));
}


/**
 * USEFUL EXTRA PROPAGATION RULES FROM PAPER "An algorithm for QBF and experimental evaluation":
 *
 * forall reduction in qdimacs format: if a clause only contains universally quantified
 * literals, then it has to be a tautology or it is unsat (so anyway it can be dropped)
 * => need to store the quantifier of variables
 *
 * all clauses only containing existentially quantified vars have to be SAT or whole problem is UNSAT.
 * => SAT CALL
 * Initially, take all clauses only containing EQ vars.
 * Later, take all clauses containing EQ vars and decided UQ vars.
 * => Simulate by taking full theory, replace all literals = \lnot UQ var with a new var (#atoms+var), and make
 * 		all true that have not yet been decided.
 * Then incremental SAT solving with assumptions
 *
 * if the theory with all universally quantified vars dropped is SAT, then the whole theory is SAT
 * => SAT CALL
 * Initially, take all clauses with all UQ left out
 * Later, take all clauses containing EQ vars and decided UQ vars, leaving out the undecided ones.
 * => Simulate by taking full theory, replace all literals = \lnot AQ var with a new var (#atoms+var), and make
 * 		all false that have not yet been decided.
 * Then incremental SAT solving with assumptions
 *
 * monotone literals can be immediately assigned a value
 *
 * propagation if a clause only contains one existentially quantified literal and only later universally
 * quantified literals.
 *
 * something called pairwise falsity
 *
 */

//void SOSolver::finishParsing(){
//	verifyHierarchy();
//	solvers[0]->finishParsingDown();
//}
//
//SATVAL SOSolver::add(int modid, const InnerSubTheory& subtheory){
//	assert(state==LOADINGHIER);
//
//	int child = subtheory.child;
//	checkexistsModSolver(modid);
//	if(sign(subtheory.head)){
//		stringstream ss;
//		ss <<">> Modal operator " <<child+1 <<" has a negative head.\n";
//		throw idpexception(ss.str());
//	}
//	if(solvers.size()<(uint)child+1){
//		solvers.resize(child+1, NULL);
//	}
//	Var head = var(subtheory.head);
//	solvers[child] = new ModSolver(child, head, this);
//	solvers[child]->setParent(modid);
//	return SATVAL::POS_SAT;
//}
//SATVAL SOSolver::add(int modid, const InnerRigidAtoms& rigid){
//	assert(state==LOADINGHIER);
//	//allAtoms.insert(allAtoms.cend(), atoms.cbegin(), atoms.cend());
//	checkexistsModSolver(modid);
//	return getModSolver(modid)->add(rigid);
//}
//
////Add information for PC-Solver
//
///**
// * Try to add the clause as high up in the hierarchy as possible.
// *
// * How can this be done: if all literals of a clause are rigid atoms, then the clause
// * if effectively relevant to the parent modal operator.
// * The sign of the modal operators decides whether the clause has to be negated or not.
// * If it is too difficult too negate it, it is not pushed upwards.
// *
// * This is only possible if the sign of the modal operator is fixed. It is guaranteed that if
// * it is certainly fixed, the head will be known at this point in time.
// *
// * Currently done substitutions
// */
//SATVAL SOSolver::add(int modid, const InnerDisjunction& disj){
//	if(state==LOADINGHIER){
//		state = LOADINGREST;
//	}
//	assert(state==LOADINGREST);
///*
//	//Check two initial propagation rules
//	bool allexist = true;
//	litlist onlyexists;
//	for(int i=0; i<lits.size(); ++i){
//		if(isForall(lits[i])){
//			allexist = false;
//		}else{
//			onlyexists.push(lits[i]);
//			//TODO forall reduction necessary!
//		}
//	}
//	if(allexist){
//		initialsolverone->addClause(lits);
//	}
//	initialsolvertwo->addClause(onlyexists);*/
//
//	//Try to add a clause as high up in the hierarchy as possible.
//	const litlist& lits = disj.literals;
//	checkexistsModSolver(modid);
//	uint previd = modid, currentid = modid;
//	ModSolver* m = NULL;
//	bool negated = false;
//	while(true){
//		m = getModSolver(currentid);
//		bool alloccur = true;
//		for(uint i=0; alloccur && i<lits.size(); ++i){
//			bool seen = false;
//			for(vector<Var>::const_iterator j=m->getAtoms().cbegin(); !seen && j<m->getAtoms().cend(); ++j){
//				if(*j==var(lits[i])){
//					seen = true;
//				}
//			}
//			if(!seen){
//				alloccur = false;
//			}
//		}
//		if(!alloccur){
//			break;
//		}
//		int parentid = m->getParentId();
//		if(parentid==-1){
//			break;
//		}else{
//			if(m->getHeadValue()==l_Undef){
//				break;
//			}else if(m->getHeadValue()==l_False){
//				negated = !negated;
//			}
//		}
//		currentid = parentid;
//		if(!negated){
//			 previd = currentid;
//		}
//	}
//	SATVAL result;
//	if(negated){
//		result = getModSolver(previd)->add(disj);
//	}else{
//		result = getModSolver(currentid)->add(disj);
//	}
//	return result;
//}
//
//SATVAL SOSolver::add(int modid, const InnerRule& rule){
//	return getModSolverDuringAdding(modid).add(rule);
//}
//SATVAL SOSolver::add(int modid, const InnerWLSet& wset){
//	return getModSolverDuringAdding(modid).add(wset);
//}
//SATVAL SOSolver::add(int modid, const InnerAggregate& agg){
//	return getModSolverDuringAdding(modid).add(agg);
//}
//SATVAL SOSolver::add(int modid, const InnerReifAggregate& agg){
//	return getModSolverDuringAdding(modid).add(agg);
//}
//
///**
// * Verifies whether the hierarchy is indeed a tree:
// * no loops exist
// * no-one is child of more than one solver
// * no solver has no parent unless it is the root
// *
// * Algorithm:
// * go through the tree BREADTH-FIRST, starting from the root
// * remember whether a solver has been seen and how many times
// */
////TODO: should verify that any head only occurs in the theory of the parent modal solver.
//void SOSolver::verifyHierarchy(){
//	assert(state == ALLLOADED);
//
//	vector<uint> queue;
//	vector<int> visitcount(solvers.size(), 0);
//	queue.push_back(0);
//	++visitcount[0];
//	while(queue.size()>0){
//		uint s = queue.back();
//		queue.pop_back();
//		ModSolver* solver = getModSolver(s);
//		for(vmodindex::const_iterator i=getSolver()->getChildren().cbegin(); i<getSolver()->getChildren().cend(); ++i){
//			if(visitcount[*i]==0){
//				queue.push_back(*i);
//			}
//			++visitcount[*i];
//		}
//	}
//	for(vmsolvers::const_iterator i=solvers.cbegin(); i<solvers.cend(); ++i){
//		if(visitcount[(*i)->getId()]!=1 && *i!=NULL){
//			stringstream ss;
//			ss <<">>The hierarchy of modal solvers does not form a tree. ";
//			ss <<"The Solver with id " <<(*i)->getPrintId() <<"is ";
//			ss <<(visitcount[(*i)->getId()]==0?"not referenced":"referenced multiple times");
//			ss <<".\n";
//			throw idpexception(ss.str());
//		}
//	}
//}
