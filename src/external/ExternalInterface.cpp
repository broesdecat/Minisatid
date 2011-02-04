//------------------------------------------------------------------------------
// Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
//
// This file is part of MinisatID.
//
// MinisatID is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MinisatID is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
//------------------------------------------------------------------------------

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

///////
// PROP SOLVER
 ///////

WrappedPCSolver::WrappedPCSolver(const SolverOption& modes)
		:WrappedLogicSolver(), _impl(new WPCLSImpl(modes)){
}

WrappedPCSolver::~WrappedPCSolver(){
	delete _impl;
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

bool WrappedPCSolver::addRule(bool conj, Literal head, const vector<Literal>& lits){
	return getImpl()->addRule(conj, head, lits);
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

///////
// MODEL SOLVER
///////

WrappedSOSolver::WrappedSOSolver(const SolverOption& modes):
		WrappedLogicSolver(), _impl(new WSOLSImpl(modes)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete _impl;
}

void WrappedSOSolver::addVar(vsize modid, Atom v){
	getImpl()->addVar(modid, v);
}

bool WrappedSOSolver::addClause(vsize modid, vector<Literal>& lits){
	return getImpl()->addClause(modid, lits);
}

bool WrappedSOSolver::addRule(vsize modid, bool conj, Atom head, vector<Literal>& lits){
	return getImpl()->addRule(modid, conj, Literal(head, false), lits);
}

bool WrappedSOSolver::addSet(vsize modid, int id, vector<Literal>& lits, vector<Weight>& w){
	return getImpl()->addSet(modid, id, lits, w);
}

//Might be implemented more efficiently in the future
bool WrappedSOSolver::addSet(vsize modid, int id, vector<WLtuple>& lws){
	return getImpl()->addSet(modid, id, lws);
}

bool WrappedSOSolver::addAggrExpr(vsize modid, Literal head, int setid, const Weight& bound, AggSign sign, AggType type, AggSem sem){
	return getImpl()->addAggrExpr(modid, head, setid, bound, sign, type, sem);
}

//Add information for hierarchy
bool WrappedSOSolver::addChild(vsize parent, vsize child, Literal head){
	return getImpl()->addChild(parent, child, head);
}

bool WrappedSOSolver::addAtoms(vsize modid, const vector<Atom>& atoms){
	return getImpl()->addAtoms(modid, atoms);
}
