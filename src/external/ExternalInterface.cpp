/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/ExternalInterface.hpp"
#include "external/InterfaceImpl.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

WrappedLogicSolver::WrappedLogicSolver(){}

WrappedLogicSolver::~WrappedLogicSolver(){
}

void WrappedLogicSolver::setTranslator(Translator* translator){
	getImpl()->setTranslator(translator);
}

bool WrappedLogicSolver::hasOptimization() const {
	return getImpl()->hasOptimization();
}

Translator& WrappedLogicSolver::getTranslator() {
	return getImpl()->getTranslator();
}

void WrappedLogicSolver::notifyTimeout() const {
	getImpl()->notifyTimeout();
}

void WrappedLogicSolver::printStatistics() const {
	getImpl()->printStatistics();
}

bool WrappedLogicSolver::solve(Solution* sol){
	return getImpl()->solve(sol);
}

// PROPOSITIONAL SOLVER

WrappedPCSolver::WrappedPCSolver(const SolverOption& modes)
		:WrappedLogicSolver(), impl(new WPCLSImpl(modes)){
}

WrappedPCSolver::~WrappedPCSolver(){
	delete impl;
}

void WrappedPCSolver::addVar(Atom v){
	getPCImpl()->addVar(v);
}

bool WrappedPCSolver::addClause(vector<Literal>& lits){
	return getPCImpl()->addClause(lits);
}

bool WrappedPCSolver::addEquivalence(const Literal& head, const vector<Literal>& body, bool conj){
	return getPCImpl()->addEquivalence(head, body, conj);
}

bool WrappedPCSolver::addConjRule(Atom head, const vector<Literal>& lits){
	return getPCImpl()->addRule(true, Literal(head, false), lits);
}

bool WrappedPCSolver::addDisjRule(Atom head, const vector<Literal>& lits){
	return getPCImpl()->addRule(false, Literal(head, false), lits);
}

bool WrappedPCSolver::addConjRuleToID(int defid, Atom head, const vector<Literal>& lits){
	return getPCImpl()->addRuleToID(defid, true, Literal(head, false), lits);
}

bool WrappedPCSolver::addDisjRuleToID(int defid, Atom head, const vector<Literal>& lits){
	return getPCImpl()->addRuleToID(defid, false, Literal(head, false), lits);
}

bool WrappedPCSolver::addSet(int id, const vector<Literal>& lits){
	return getPCImpl()->addSet(id, lits);
}

bool WrappedPCSolver::addSet(int id, const vector<WLtuple>& lws){
	return getPCImpl()->addSet(id, lws);
}

bool WrappedPCSolver::addSet(int id, const vector<Literal>& lits, const vector<Weight>& w){
	return getPCImpl()->addSet(id, lits, w);
}

bool WrappedPCSolver::addAggrExpr(Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getPCImpl()->addAggrExpr(head, setid, bound, sign, type, sem);
}

bool WrappedPCSolver::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	return getPCImpl()->addMinimize(lits, subsetmnmz);
}

bool WrappedPCSolver::addMinimize(const Atom head, const int setid, AggType type){
	return getPCImpl()->addMinimize(head, setid, type);
}

bool WrappedPCSolver::addIntVar(int groundname, int min, int max){
	return getPCImpl()->addIntVar(groundname, min, max);
}

bool WrappedPCSolver::addCPBinaryRel(Literal head, int groundname, EqType rel, int bound){
	return getPCImpl()->addCPBinaryRel(head, groundname, rel, bound);
}

bool WrappedPCSolver::addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2){
	return getPCImpl()->addCPBinaryRelVar(head, groundname, rel, groundname2);
}

bool WrappedPCSolver::addCPSum(Literal head, const vector<int>& termnames, EqType rel, int bound){
	return getPCImpl()->addCPSum(head, termnames, rel, bound);
}

bool WrappedPCSolver::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int bound){
	return getPCImpl()->addCPSum(head, termnames, mult, rel, bound);
}

bool WrappedPCSolver::addCPSumVar(Literal head, const vector<int>& termnames, EqType rel, int rhstermname){
	return getPCImpl()->addCPSumVar(head, termnames, rel, rhstermname);
}

bool WrappedPCSolver::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int rhstermname){
	return getPCImpl()->addCPSumVar(head, termnames, mult, rel, rhstermname);
}

bool WrappedPCSolver::addCPCount(const vector<int>& termnames, int value, EqType rel, int rhstermname){
	return getPCImpl()->addCPCount(termnames, value, rel, rhstermname);
}

bool WrappedPCSolver::addCPAlldifferent(const vector<int>& termnames){
	return getPCImpl()->addCPAlldifferent(termnames);
}

void WrappedPCSolver::addForcedChoices(const vector<Literal> lits){
	getPCImpl()->addForcedChoices(lits);
}

WLSImpl* WrappedPCSolver::getImpl() const {
	return impl;
}

WPCLSImpl* WrappedPCSolver::getPCImpl() const {
	return impl;
}

// MODAL SOLVER

WrappedSOSolver::WrappedSOSolver(const SolverOption& modes):
		WrappedLogicSolver(), _impl(new WSOLSImpl(modes)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete _impl;
}

WLSImpl* WrappedSOSolver::getImpl() const {
	return _impl;
}

WSOLSImpl* WrappedSOSolver::getSOImpl() const {
	return _impl;
}

void WrappedSOSolver::addVar(int modid, Atom v){
	getSOImpl()->addVar(modid, v);
}

bool WrappedSOSolver::addClause(int modid, vector<Literal>& lits){
	return getSOImpl()->addClause(modid, lits);
}

bool WrappedSOSolver::addConjRule(int modid, Atom head, vector<Literal>& lits){
	return getSOImpl()->addRule(modid, true, Literal(head, false), lits);
}

bool WrappedSOSolver::addDisjRule(int modid, Atom head, vector<Literal>& lits){
	return getSOImpl()->addRule(modid, false, Literal(head, false), lits);
}

bool WrappedSOSolver::addSet(int modid, int id, vector<Literal>& lits, vector<Weight>& w){
	return getSOImpl()->addSet(modid, id, lits, w);
}

//Might be implemented more efficiently in the future
bool WrappedSOSolver::addSet(int modid, int id, vector<WLtuple>& lws){
	return getSOImpl()->addSet(modid, id, lws);
}

bool WrappedSOSolver::addAggrExpr(int modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getSOImpl()->addAggrExpr(modid, head, setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool WrappedSOSolver::addSubTheory(int parent, Literal head, int child){
	return getSOImpl()->addChild(parent, child, head);
}

bool WrappedSOSolver::addRigidAtoms(int modid, const vector<Atom>& atoms){
	return getSOImpl()->addAtoms(modid, atoms);
}
