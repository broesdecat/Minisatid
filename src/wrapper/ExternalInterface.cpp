/*
 * Copyright 2007-2011 Katholieke Universiteit Leuven
 *
 * Use of this software is governed by the GNU LGPLv3.0 license
 *
 * Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
 * Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
 */
#include "external/ExternalInterface.hpp"
#include "wrapper/InterfaceImpl.hpp"
#include "external/SearchMonitor.hpp"

#include "external/LazyClauseSupport.hpp"

using namespace std;
using namespace MinisatID;

SATVAL MinisatID::operator&= (SATVAL orig, SATVAL add){
	return (orig==SATVAL::UNSAT||add==SATVAL::UNSAT)? SATVAL::UNSAT: SATVAL::POS_SAT;
}

WrappedLogicSolver::WrappedLogicSolver(){}

WrappedLogicSolver::~WrappedLogicSolver(){
}

bool WrappedLogicSolver::hasOptimization() const {
	return getImpl()->hasOptimization();
}

void WrappedLogicSolver::printStatistics() const {
	getImpl()->printStatistics();
}

void WrappedLogicSolver::solve(Solution* sol){
	getImpl()->setSolutionMonitor(sol);
	getImpl()->solve();
}

void WrappedLogicSolver::printTheory(ostream& stream, Solution* sol) const{
	getImpl()->setSolutionMonitor(sol);
	getImpl()->printTheory(stream);
}

void WrappedLogicSolver::addMonitor(SearchMonitor* const monitor){
	getImpl()->addMonitor(monitor);
}



WrappedPCSolver::WrappedPCSolver(const SolverOption& modes)
		:WrappedLogicSolver(), impl(new PCWrapperPimpl(modes)){
}

WrappedPCSolver::~WrappedPCSolver(){
	delete impl;
}

WrapperPimpl* WrappedPCSolver::getImpl() const {
	return impl;
}

PCWrapperPimpl* WrappedPCSolver::getPCImpl() const {
	return impl;
}

template<class T>
SATVAL WrappedPCSolver::add(const T& sentence){
	return getPCImpl()->add<T>(sentence);
}

WrappedSOSolver::WrappedSOSolver(const SolverOption& modes):
		WrappedLogicSolver(), impl(new SOWrapperPimpl(modes)){
}

WrappedSOSolver::~WrappedSOSolver(){
	delete impl;
}

WrapperPimpl* WrappedSOSolver::getImpl() const {
	return impl;
}

SOWrapperPimpl* WrappedSOSolver::getSOImpl() const {
	return impl;
}

template<class T>
SATVAL WrappedSOSolver::add(int modalid, const T& sentence){
	return getSOImpl()->add(modalid, sentence);
}

// Only those explicitly instantiated (here or elsewhere) will be available in a compiled library
template SATVAL WrappedPCSolver::add(const Disjunction& sentence);
template SATVAL WrappedPCSolver::add(const DisjunctionRef& sentence);
template SATVAL WrappedPCSolver::add(const Equivalence& sentence);
template SATVAL WrappedPCSolver::add(const Rule& sentence);
template SATVAL WrappedPCSolver::add(const Set& sentence);
template SATVAL WrappedPCSolver::add(const WSet& sentence);
template SATVAL WrappedPCSolver::add(const WLSet& sentence);
template SATVAL WrappedPCSolver::add(const Aggregate& sentence);
template SATVAL WrappedPCSolver::add(const MinimizeSubset& sentence);
template SATVAL WrappedPCSolver::add(const MinimizeOrderedList& sentence);
template SATVAL WrappedPCSolver::add(const MinimizeVar& sentence);
template SATVAL WrappedPCSolver::add(const MinimizeAgg& sentence);
template SATVAL WrappedPCSolver::add(const CPIntVarRange& sentence);
template SATVAL WrappedPCSolver::add(const CPIntVarEnum& sentence);
template SATVAL WrappedPCSolver::add(const CPBinaryRel& sentence);
template SATVAL WrappedPCSolver::add(const CPBinaryRelVar& sentence);
template SATVAL WrappedPCSolver::add(const CPSumWeighted& sentence);
template SATVAL WrappedPCSolver::add(const CPCount& sentence);
template SATVAL WrappedPCSolver::add(const CPAllDiff& sentence);
template SATVAL WrappedPCSolver::add(const ForcedChoices& sentence);
template SATVAL WrappedPCSolver::add(const SymmetryLiterals& sentence);
template SATVAL WrappedPCSolver::add(const Symmetry& sentence);
template SATVAL WrappedPCSolver::add(const LazyGroundLit& sentence);

template SATVAL WrappedSOSolver::add(int modalid, const Disjunction& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const DisjunctionRef& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const Rule& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const Set& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const WSet& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const WLSet& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const Aggregate& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const RigidAtoms& sentence);
template SATVAL WrappedSOSolver::add(int modalid, const SubTheory& sentence);
