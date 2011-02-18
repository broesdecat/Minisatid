/* * Copyright 2007-2011 Katholieke Universiteit Leuven * * Use of this software is governed by the GNU LGPLv3.0 license * * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium */
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

void WrappedPCSolver::addForcedChoices(const vector<Literal> lits){
	getImpl()->addForcedChoices(lits);
}

void WrappedLogicSolver::printStatistics() const {
	getImpl()->printStatistics();
}

bool WrappedLogicSolver::finishParsing(){
	return getImpl()->finishParsing();
}

bool WrappedLogicSolver::simplify(){
	return getImpl()->simplify();
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
	getImpl()->addVar(v);
}

bool WrappedPCSolver::addClause(vector<Literal>& lits){
	return getImpl()->addClause(lits);
}

bool WrappedPCSolver::addEquivalence(const Literal& head, const vector<Literal>& body, bool conj){
	return getImpl()->addEquivalence(head, body, conj);
}

bool WrappedPCSolver::addConjRule(Atom head, const vector<Literal>& lits){
	return getImpl()->addRule(true, Literal(head, false), lits);
}

bool WrappedPCSolver::addDisjRule(Atom head, const vector<Literal>& lits){
	return getImpl()->addRule(false, Literal(head, false), lits);
}

bool WrappedPCSolver::addConjRuleToID(int defid, Atom head, const vector<Literal>& lits){
	return getImpl()->addRuleToID(defid, true, Literal(head, false), lits);
}

bool WrappedPCSolver::addDisjRuleToID(int defid, Atom head, const vector<Literal>& lits){
	return getImpl()->addRuleToID(defid, false, Literal(head, false), lits);
}

bool WrappedPCSolver::addSet(int id, const vector<Literal>& lits){
	return getImpl()->addSet(id, lits);
}

bool WrappedPCSolver::addSet(int id, const vector<WLtuple>& lws){
	return getImpl()->addSet(id, lws);
}

bool WrappedPCSolver::addSet(int id, const vector<Literal>& lits, const vector<Weight>& w){
	return getImpl()->addSet(id, lits, w);
}

bool WrappedPCSolver::addAggrExpr(Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getImpl()->addAggrExpr(head, setid, bound, sign, type, sem);
}

bool WrappedPCSolver::addMinimize(const vector<Literal>& lits, bool subsetmnmz){
	return getImpl()->addMinimize(lits, subsetmnmz);
}

bool WrappedPCSolver::addMinimize(const Atom head, const int setid, AggType type){
	return getImpl()->addMinimize(head, setid, type);
}

bool WrappedPCSolver::addIntVar(int groundname, int min, int max){
	return getImpl()->addIntVar(groundname, min, max);
}

bool WrappedPCSolver::addCPBinaryRel(Literal head, int groundname, EqType rel, int bound){
	return getImpl()->addCPBinaryRel(head, groundname, rel, bound);
}

bool WrappedPCSolver::addCPBinaryRelVar(Literal head, int groundname, EqType rel, int groundname2){
	return getImpl()->addCPBinaryRelVar(head, groundname, rel, groundname2);
}

bool WrappedPCSolver::addCPSum(Literal head, const vector<int>& termnames, EqType rel, int bound){
	return getImpl()->addCPSum(head, termnames, rel, bound);
}

bool WrappedPCSolver::addCPSum(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int bound){
	return getImpl()->addCPSum(head, termnames, mult, rel, bound);
}

bool WrappedPCSolver::addCPSumVar(Literal head, const vector<int>& termnames, EqType rel, int rhstermname){
	return getImpl()->addCPSumVar(head, termnames, rel, rhstermname);
}

bool WrappedPCSolver::addCPSumVar(Literal head, const vector<int>& termnames, vector<int> mult, EqType rel, int rhstermname){
	return getImpl()->addCPSumVar(head, termnames, mult, rel, rhstermname);
}

bool WrappedPCSolver::addCPCount(const vector<int>& termnames, int value, EqType rel, int rhstermname){
	return getImpl()->addCPCount(termnames, value, rel, rhstermname);
}

bool WrappedPCSolver::addCPAlldifferent(const vector<int>& termnames){
	return getImpl()->addCPAlldifferent(termnames);
}

// MODAL SOLVER

WrappedSOSolver::WrappedSOSolver(const SolverOption& modes):
		WrappedLogicSolver(), _impl(new WSOLSImpl(modes)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete _impl;
}

void WrappedSOSolver::addVar(int modid, Atom v){
	getImpl()->addVar(modid, v);
}

bool WrappedSOSolver::addClause(int modid, vector<Literal>& lits){
	return getImpl()->addClause(modid, lits);
}

bool WrappedSOSolver::addConjRule(int modid, Atom head, vector<Literal>& lits){
	return getImpl()->addRule(modid, true, Literal(head, false), lits);
}

bool WrappedSOSolver::addDisjRule(int modid, Atom head, vector<Literal>& lits){
	return getImpl()->addRule(modid, false, Literal(head, false), lits);
}

bool WrappedSOSolver::addSet(int modid, int id, vector<Literal>& lits, vector<Weight>& w){
	return getImpl()->addSet(modid, id, lits, w);
}

//Might be implemented more efficiently in the future
bool WrappedSOSolver::addSet(int modid, int id, vector<WLtuple>& lws){
	return getImpl()->addSet(modid, id, lws);
}

bool WrappedSOSolver::addAggrExpr(int modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getImpl()->addAggrExpr(modid, head, setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool WrappedSOSolver::addSubTheory(int parent, Literal head, int child){
	return getImpl()->addChild(parent, child, head);
}

bool WrappedSOSolver::addRigidAtoms(int modid, const vector<Atom>& atoms){
	return getImpl()->addAtoms(modid, atoms);
}
