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

using namespace MinisatID;
using namespace std;

SearchEngine::~SearchEngine(){
	delete(solver);
}

PropagatorFactory& SearchEngine::getFactory() {
	return solver->getFactory();
}
void SearchEngine::createVar(Var v) {
	solver->createVar(v);
}
int SearchEngine::verbosity() const {
	return solver->verbosity();
}
const SolverOption& SearchEngine::modes() const {
	return solver->modes();
}
Var SearchEngine::newVar() {
	return solver->newVar();
}
int SearchEngine::newSetID() {
	return solver->newSetID();
}
lbool SearchEngine::rootValue(Lit p) const {
	return solver->rootValue(p);
}
Lit SearchEngine::getTrueLit() const {
	return solver->getTrueLit();
}
Lit SearchEngine::getFalseLit() const {
	return solver->getFalseLit();
}

void SearchEngine::notifyUnsat() {
	solver->notifyUnsat();
}
SATVAL SearchEngine::satState() const {
	return solver->satState();
}
bool SearchEngine::isUnsat() const {
	return solver->isUnsat();
}
std::string SearchEngine::toString(const Lit& lit) const {
	return solver->toString(lit);
}

void SearchEngine::invalidate(litlist& clause) const {
	solver->invalidate(clause);
}

void SearchEngine::finishParsing() {
	solver->finishParsing();
}
bool SearchEngine::isOptimizationProblem() const {
	return solver->isOptimizationProblem();
}
bool SearchEngine::isAlwaysAtOptimum() const{
	return solver->isAlwaysAtOptimum();
}
bool SearchEngine::hasNextOptimum() const {
	return solver->hasNextOptimum();
}
OptimStatement& SearchEngine::getNextOptimum() {
	return solver->getNextOptimum();
}

bool SearchEngine::hasCPSolver() const {
	return solver->hasCPSolver();
}
SATVAL SearchEngine::findNextCPModel() {
	return solver->findNextCPModel();
}

void SearchEngine::notifyTerminateRequested() {
	solver->notifyTerminateRequested();
}

void SearchEngine::saveState() {
	solver->saveState();
}
void SearchEngine::resetState() {
	solver->resetState();
}

void SearchEngine::extractLitModel(std::shared_ptr<Model> fullmodel) {
	solver->extractLitModel(fullmodel);
}
void SearchEngine::extractVarModel(std::shared_ptr<Model> fullmodel) {
	solver->extractVarModel(fullmodel);
}
std::shared_ptr<Model> SearchEngine::getModel() {
	return solver->getModel();
}
lbool SearchEngine::getModelValue(Var v) {
	return solver->getModelValue(v);
}

void SearchEngine::accept(ConstraintVisitor& visitor) {
	solver->accept(visitor);
}

void SearchEngine::setAssumptions(const litlist& assumps) {
	solver->setAssumptions(assumps);
}
lbool SearchEngine::solve(bool search) {
	return solver->solve(search);
}
litlist SearchEngine::getUnsatExplanation() const{
	return solver->getUnsatExplanation();
}

litlist SearchEngine::getEntailedLiterals() const {
	return solver->getEntailedLiterals();
}
bool SearchEngine::moreModelsPossible() const {
	return solver->moreModelsPossible();
}
